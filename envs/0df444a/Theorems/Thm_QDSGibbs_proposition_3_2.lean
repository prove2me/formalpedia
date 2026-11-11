-- Prove2me | Theorems.Thm_QDSGibbs_proposition_3_2
-- name    : QDSGibbs.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:34.6638+00:00
-- url     : https://prove2.me/theorems/6ded77bd-1f01-46d1-8b3d-68b83308fdcb
-- title:
--   Proposition 3.2 — QBP identity and norm bounds for $O_B$
-- statement:
--   Let $H$ be a Hamiltonian given by a labelled interaction with Hermitian on-site terms and Hermitian interaction terms, $B$ a block, $\beta>0$, $H^0_B=H_B+H_{B^c}$ and $W_{\partial B}=H-H^0_B$. Let $O_B(u)$ solve (3.6) along $H_B(u)=H^0_B+uW_{\partial B}$ and $O_B=O_B(1)$. Then every $O_B(u)$, $0\le u\le1$, is invertible, and
--
--   $$
--   O_Be^{-\beta H^0_B/2}O_B^*=e^{-\beta H/2},\qquad \|O_B^{\pm1}\|\le e^{\beta\|W_{\partial B}\|/4},\qquad \|O_B-\mathbb 1\|+\|O_B^{-1}-\mathbb 1\|\le2\big(e^{\beta\|W_{\partial B}\|/4}-1\big).
--   $$
--
--   More generally, for every $0\le u\le v\le1$,
--
--   $$
--   \max\big\{\|O_B(v)O_B(u)^{-1}\|,\ \|O_B(u)O_B(v)^{-1}\|\big\}\le e^{(v-u)\beta\|W_{\partial B}\|/4}.
--   $$
--
--   This is Hastings' quantum belief propagation identity at inverse temperature $\beta/2$; it is what makes the dressed reset preserve the full Gibbs state.
--
--   Differences from the source:
--   - generalization: a Hamiltonian (2.1) with $2\le|X_\alpha|\le k$, $\operatorname{diam}X_\alpha\le r$, each site in at most $\nu$ supports → any finite labelled family $(h_\alpha, X_\alpha)$ with Hermitian terms supported on $X_\alpha$ and Hermitian on-site terms (`Interaction.IsValid`); reason: the statement and its proof do not use the bookkeeping bounds; every Hamiltonian (2.1) is such a family
--   - encoding: $O_B(u)$, the solution of (3.6) on $[0,1]$ → the solution on all of $\mathbb R$ chosen by `Classical.epsilon` (entrywise derivatives); reason: the linear ODE has continuous coefficients, so the global solution exists, is unique, and restricts to the paper's
--   - encoding: operators on a region $U$, partial traces $\mathrm{Tr}_S$, marginals and restricted Gibbs states acting on the subsystem → full-space matrices on $\prod_i \mathrm{Fin}\,d_i$: $A\otimes\mathbb 1$, `ptr S X` $=\mathbb 1_S\otimes\mathrm{Tr}_S X$, `gibbs β (hamOn I Ω)` $=\sigma^\Omega_\beta\otimes\mathbb 1/\dim$; reason: the paper extends operators by the identity in full-system expressions (p.10); norms, traces of products and covariances are unchanged
--   - reading: $O_B^{-1}$, $O_B(u)^{-1}$ (invertibility presupposed) → invertibility of $O_B(u)$ for $u\in[0,1]$ stated as a conclusion; reason: Mathlib's matrix inverse is $0$ on singular matrices; asserting invertibility is the stronger reading
--   - reading: local dimensions $2\le d_i\le d$ (standing) → local dimensions $d_i\ge2$; reason: the upper bound $d$ plays no role; any finite family has one
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Proposition 3.2, p.17

import Mathlib
import Definitions.Def_QDSGibbs_qbpOp

open scoped Matrix

namespace QDSGibbs

/-- **Proposition 3.2** (arXiv:2610.03578, held file sha256 ede55815…, Proposition 3.2, p.17). The
QBP operator `O_B` of (3.6) satisfies
`O_B e^{−βH⁰_B/2} O_B^* = e^{−βH/2}` (3.7), `‖O_B^{±1}‖ ≤ e^{β‖W_∂B‖/4}` (3.8),
`‖O_B − 1‖ + ‖O_B^{−1} − 1‖ ≤ 2(e^{β‖W_∂B‖/4} − 1)` (3.9), and, for `0 ≤ u ≤ v ≤ 1`,
`max{‖O_B(v)O_B(u)^{−1}‖, ‖O_B(u)O_B(v)^{−1}‖} ≤ e^{(v−u)β‖W_∂B‖/4}` (3.10).

**Formalization Note** General labelled interaction (2.1) without the bookkeeping bounds
(`Interaction.IsValid`), any block `B`, `β > 0`. `O_B(u) = qbpPathOp β I B univ u` (the path
`H_B(u) = H⁰_B + uW_∂B`), `O_B = O_B(1)`, `H⁰_B = H_B + H_{B^c}`. The statement presupposes that the
`O_B(u)` are invertible; this is stated as the first clause, since Mathlib's inverse of a singular
matrix is `0`. `‖·‖` is the operator norm. -/
theorem proposition_3_2 {N : ℕ} (d : Fin N → ℕ) (hd : ∀ i, 2 ≤ d i) (I : Interaction d)
    (hI : I.IsValid) (B : Finset (Fin N)) (β : ℝ) (hβ : 0 < β) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 → IsUnit (qbpPathOp β I B Finset.univ u)) ∧
    qbpOp β I B Finset.univ * NormedSpace.exp ((-(β / 2)) • (hamOn I B + hamOn I Bᶜ)) *
        (qbpOp β I B Finset.univ)ᴴ = NormedSpace.exp ((-(β / 2)) • ham I) ∧
    opNorm (qbpOp β I B Finset.univ) ≤ Real.exp (β * opNorm (cross I B) / 4) ∧
    opNorm (qbpOp β I B Finset.univ)⁻¹ ≤ Real.exp (β * opNorm (cross I B) / 4) ∧
    opNorm (qbpOp β I B Finset.univ - 1) + opNorm ((qbpOp β I B Finset.univ)⁻¹ - 1) ≤
      2 * (Real.exp (β * opNorm (cross I B) / 4) - 1) ∧
    ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ 1 →
      max (opNorm (qbpPathOp β I B Finset.univ v * (qbpPathOp β I B Finset.univ u)⁻¹))
          (opNorm (qbpPathOp β I B Finset.univ u * (qbpPathOp β I B Finset.univ v)⁻¹)) ≤
        Real.exp ((v - u) * β * opNorm (cross I B) / 4) := by sorry

end QDSGibbs
