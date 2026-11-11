-- Prove2me | Theorems.Thm_QDSGibbs_lemma_3_5
-- name    : QDSGibbs.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:37:32.510578+00:00
-- url     : https://prove2.me/theorems/dd7f3655-a7fe-4577-b6e7-b1de7b731612
-- title:
--   Lemma 3.5 — bounds on $S_B$ and $\|\mathcal T_B\|_\diamond$, also for restricted Hamiltonians
-- statement:
--   For a labelled interaction with Hermitian terms, a block $B$, $\beta>0$ and $w_B=\|W_{\partial B}\|$, the loss operator and jump map of (3.14) satisfy
--
--   $$
--   e^{-\beta w_B}\mathbb 1\le S_B\le e^{\beta w_B}\mathbb 1,\qquad \|\mathcal T_B\|_\diamond=\|S_B\|\le e^{\beta w_B}.
--   $$
--
--   These estimates also hold when (3.6) is solved with a restricted Hamiltonian $H_\Omega$, keeping the same boundary interaction $W_{\partial B}$ and reset channel $\mathcal R_B$.
--
--   The bounds depend on the block only through its crossing interaction, which is what makes long blocks affordable in one dimension.
--
--   **Formalization Note** Stated for every region $\Omega$ (path $H_\Omega-(1-u)W_{\partial B}$); $\Omega=\Lambda$ is the first sentence. Operator inequalities are in the Loewner order.
--
--   Differences from the source:
--   - generalization: a Hamiltonian (2.1) with $2\le|X_\alpha|\le k$, $\operatorname{diam}X_\alpha\le r$, each site in at most $\nu$ supports → any finite labelled family $(h_\alpha, X_\alpha)$ with Hermitian terms supported on $X_\alpha$ and Hermitian on-site terms (`Interaction.IsValid`); reason: the statement and its proof do not use the bookkeeping bounds; every Hamiltonian (2.1) is such a family
--   - encoding: $O_B(u)$, the solution of (3.6) on $[0,1]$ → the solution on all of $\mathbb R$ chosen by `Classical.epsilon` (entrywise derivatives); reason: the linear ODE has continuous coefficients, so the global solution exists, is unique, and restricts to the paper's
--   - encoding: operators on a region $U$, partial traces $\mathrm{Tr}_S$, marginals and restricted Gibbs states acting on the subsystem → full-space matrices on $\prod_i \mathrm{Fin}\,d_i$: $A\otimes\mathbb 1$, `ptr S X` $=\mathbb 1_S\otimes\mathrm{Tr}_S X$, `gibbs β (hamOn I Ω)` $=\sigma^\Omega_\beta\otimes\mathbb 1/\dim$; reason: the paper extends operators by the identity in full-system expressions (p.10); norms, traces of products and covariances are unchanged
--   - encoding: real-valued $\|\cdot\|_{W_1}$, $D_\Psi(j)$, $\|\cdot\|_\diamond$ → values in $[0,\infty]$ (`ℝ≥0∞`); reason: the same values on the inputs the paper considers; an empty infimum or unbounded supremum gives $\infty$ instead of a junk $0$
--   - reading: local dimensions $2\le d_i\le d$ (standing) → local dimensions $d_i\ge2$; reason: the upper bound $d$ plays no role
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Lemma 3.5, p.20

import Mathlib
import Definitions.Def_QDSGibbs_blockChannel

open scoped Matrix ENNReal ComplexOrder

namespace QDSGibbs

/-- **Lemma 3.5** (arXiv:2610.03578, held file sha256 ede55815…, Lemma 3.5, p.20). The construction
satisfies `e^{−βw_B} 1 ≤ S_B ≤ e^{βw_B} 1` and `‖T_B‖⋄ = ‖S_B‖ ≤ e^{βw_B}` (3.15),
`w_B = ‖W_∂B‖`. These estimates also hold when (3.6) is solved with a restricted Hamiltonian, keeping
the same boundary interaction and reset channel.

**Formalization Note** Stated for every region `Ω`: the QBP path is `H_Ω − (1−u)W_∂B`
(`qbpPath I B Ω`) with the same `W_∂B` and the same reset `R_B`; `Ω = univ` is the first sentence and
the other `Ω` are the restricted Hamiltonians of the second. `≤` between operators is the Loewner
order (`PosSemidef` of the difference); `‖·‖⋄` is `ℝ≥0∞`-valued. -/
theorem lemma_3_5 {N : ℕ} (d : Fin N → ℕ) (hd : ∀ i, 2 ≤ d i) (I : Interaction d)
    (hI : I.IsValid) (B : Finset (Fin N)) (β : ℝ) (hβ : 0 < β) (Ω : Finset (Fin N)) :
    (sOp β I B Ω - ((Real.exp (-(β * opNorm (cross I B))) : ℝ) : ℂ) • (1 : Op d)).PosSemidef ∧
    (((Real.exp (β * opNorm (cross I B)) : ℝ) : ℂ) • (1 : Op d) - sOp β I B Ω).PosSemidef ∧
    diamondNorm (jumpMap β I B Ω) = ENNReal.ofReal (opNorm (sOp β I B Ω)) ∧
    opNorm (sOp β I B Ω) ≤ Real.exp (β * opNorm (cross I B)) := by sorry

end QDSGibbs
