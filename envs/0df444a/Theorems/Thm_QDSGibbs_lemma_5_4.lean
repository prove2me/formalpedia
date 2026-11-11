-- Prove2me | Theorems.Thm_QDSGibbs_lemma_5_4
-- name    : QDSGibbs.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:39:06.295586+00:00
-- url     : https://prove2.me/theorems/89319ac7-1ae9-4488-a163-59f5c4e2a4e6
-- title:
--   Lemma 5.4 — bounds on the localized QBP operators
-- statement:
--   On a nearest-neighbour chain, set $M=e^{\beta J_{\mathrm{int}}/2}$ and $\lambda=c/(1+\beta J_{\mathrm{int}})$, with $c>0$ a universal constant small enough that $\lambda\le1$. For every interval $B$ and integer $u\ge0$, let $O_{B,u}$ be the QBP operator along $H_{C_u(B)}-(1-\theta)W_{\partial B}$. Then $O_B$ and $O_{B,u}$ are invertible, $\|O_B^{\pm1}\|,\|O_{B,u}^{\pm1}\|\le M$, and
--
--   $$
--   \|O_B-O_{B,u}\|+\|O_B^{-1}-O_{B,u}^{-1}\|\le C\beta J_{\mathrm{int}}e^{\beta J_{\mathrm{int}}/2}e^{-\lambda u}.
--   $$
--
--   The localized operators act only near the two boundary bonds of $B$, at an error decaying exponentially in the localization radius.
--
--   Differences from the source:
--   - reading: "universal constants" $c, C$ → constants chosen before the chain length, the local dimensions (any $d_i\ge2$), $\beta$ and the chain terms; reason: the paper's convention on p.39 ("$c, C$ denote universal positive constants")
--   - reading: constants ($C$, $c$, $C_d$) → constants required to be positive (and $c\le 1$ where $\lambda\le1$ is stipulated); reason: the paper's constants are positive by convention (p.39); a positive existential is the stronger reading
--   - encoding: sites $1,\dots,N$, bonds $W_i$ on $\{i,i+1\}$ → 0-based sites `Fin N`, bond `b : Fin (N−1)` on $\{b,b+1\}$; reason: a relabelling
--   - encoding: $O_B(u)$, the solution of (3.6) on $[0,1]$ → the solution on all of $\mathbb R$ chosen by `Classical.epsilon` (entrywise derivatives); reason: the linear ODE has continuous coefficients, so the global solution exists, is unique, and restricts to the paper's
--   - encoding: operators on a region $U$, partial traces $\mathrm{Tr}_S$, marginals and restricted Gibbs states acting on the subsystem → full-space matrices on $\prod_i \mathrm{Fin}\,d_i$: $A\otimes\mathbb 1$, `ptr S X` $=\mathbb 1_S\otimes\mathrm{Tr}_S X$, `gibbs β (hamOn I Ω)` $=\sigma^\Omega_\beta\otimes\mathbb 1/\dim$; reason: the paper extends operators by the identity in full-system expressions (p.10); norms, traces of products and covariances are unchanged
--   - reading: $O_B^{-1}$, $O_{B,u}^{-1}$ (invertibility presupposed) → invertibility of $O_B$ and $O_{B,u}$ stated as conclusions; reason: Mathlib's matrix inverse is $0$ on singular matrices; asserting invertibility is the stronger reading
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Lemma 5.4, p.41

import Mathlib
import Definitions.Def_QDSGibbs_chainGen

open scoped Matrix

namespace QDSGibbs

/-- **Lemma 5.4 (Bounds on the localized QBP operators)** (arXiv:2610.03578, held file sha256
ede55815…, Lemma 5.4, p.41). Set `M = e^{βJ_int/2}` and `λ = c/(1 + βJ_int)`, with `c > 0` as in
Lemma 3.10, decreased if necessary so that `λ ≤ 1`. Then `‖O_B^{±1}‖, ‖O_{B,u}^{±1}‖ ≤ M` and
`‖O_B − O_{B,u}‖ + ‖O_B^{−1} − O_{B,u}^{−1}‖ ≤ CβJ_int e^{βJ_int/2} e^{−λu}` (5.8).

**Formalization Note** `c ∈ (0, 1]` (so `λ ≤ 1`) and `C > 0` are universal: chosen before the chain
length, the local dimensions, `β > 0` and the chain terms; then the bounds hold for every interval
`B ⊆ [N]` and every integer `u ≥ 0`. `O_B = qbpOp β I B univ`, `O_{B,u} = qbpOp β I B (C_u(B))`
(the path `H_{C_u(B)} − (1−θ)W_∂B`, p.41). Invertibility of both, presupposed by `O^{−1}`, is stated
as a conclusion. -/
theorem lemma_5_4 :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < C ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (d : Fin N → ℕ), (∀ i, 2 ≤ d i) →
        ∀ (V : Fin N → Op d) (W : Fin (N - 1) → Op d), IsChainHam V W → ∀ β : ℝ, 0 < β →
          ∀ B : Finset (Fin N), IsInterval B → ∀ u : ℕ,
            IsUnit (qbpOp β (chain V W) B Finset.univ) ∧
            IsUnit (qbpOp β (chain V W) B (bdryNbhd B u)) ∧
            opNorm (qbpOp β (chain V W) B Finset.univ) ≤ Real.exp (β * jint (chain V W) / 2) ∧
            opNorm (qbpOp β (chain V W) B Finset.univ)⁻¹ ≤ Real.exp (β * jint (chain V W) / 2) ∧
            opNorm (qbpOp β (chain V W) B (bdryNbhd B u)) ≤ Real.exp (β * jint (chain V W) / 2) ∧
            opNorm (qbpOp β (chain V W) B (bdryNbhd B u))⁻¹ ≤ Real.exp (β * jint (chain V W) / 2) ∧
            opNorm (qbpOp β (chain V W) B Finset.univ - qbpOp β (chain V W) B (bdryNbhd B u)) +
                opNorm ((qbpOp β (chain V W) B Finset.univ)⁻¹ -
                  (qbpOp β (chain V W) B (bdryNbhd B u))⁻¹) ≤
              C * β * jint (chain V W) * Real.exp (β * jint (chain V W) / 2) *
                Real.exp (-(c / (1 + β * jint (chain V W))) * u) := by sorry

end QDSGibbs
