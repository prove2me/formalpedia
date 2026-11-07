-- Prove2me | Theorems.Thm_SamplingLLL_eq_A4
-- name    : SamplingLLL.eq_A4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:00:06.476195+00:00
-- url     : https://prove2.me/theorems/ba8fec6b-2431-4602-bada-23803858e143
-- title:
--   (A3), (A4) and the local operation, pp.67–68
-- statement:
--   Under $x_a\in(0,1)$, $p_a\ge\lambda(\mathrm{Bad}_a)$, (C) on $G$ and (SLL), for a task $(S,c)$ with $c\notin S$: the proposal is an executable subprobability with
--   $$
--   q_c(t)=\prod_{b\in Y\setminus\{c\}}\frac{x_b}2\prod_{d\in N\cup F_1}\Big(1-\frac{x_d}2\Big), \tag{A3}
--   $$
--   and
--   $$
--   \bar a_t\prod_{d\in D_t}\sigma_d^{-1}\le B_cq_c(t)\prod_{d\in D_t}\theta_d. \tag{A4}
--   $$
--   The thinning ratio $u_t/[B_cq_c(t)\prod_{d\in D_t}\sigma_d]$ is at most one, the combined retained mass is exactly $a_t/[B_cq_c(t)\prod_{d\in D_t}\sigma_d]$, and conditional on retention the draw has the required local law.
--
--   Differences from the source:
--   - encoding: "the combined retained mass ... and conditional on retention the draw has the required local law" → `LocalExact`: the mass of acceptance with a mark equal to $y$ on $W_t$, for every $y$; reason: these two statements together are this one identity
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), eqs. (A3), (A4), pp.67–68

import Mathlib
import Definitions.Def_SamplingLLL_sllAnalysis

set_option autoImplicit false

namespace SamplingLLL

/-- (A3), (A4) and the local operation, pp.67–68: the proposal has distribution (A3); under (SLL) and (A1)
the recordwise envelope (A4) holds; the thinning ratio is at most one; and the combined retained mass
is `a_t/[B_c q_c(t) ∏_{d∈D_t} σ_d]`, with the local draw from `λ_{W_t}(· | E_t)`, which is `LocalExact`.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), eqs. (A3), (A4), pp.67–68. -/
theorem eq_A4 {n m : ℕ} (I : AtomicCSP n m) (G : Finset (Fin m)) (x : Fin m → ℚ) (p : Fin m → ℝ)
    (hx : ∀ a, 0 < x a ∧ x a < 1) (hp : ∀ a, ((I.badProb a : ℚ) : ℝ) ≤ p a)
    (hG : ∀ a ∈ G, I.SamplingGood p a) (hSLL : I.SLL G p x)
    (S : Finset (Fin m)) (c : Fin m) (hc : c ∉ S) :
    (I.sllData G x).ProposalExact S c ∧
    ∀ t ∈ (I.sllData G x).leavesOf S c,
      (I.sllData G x).q S c t = ((I.qFormula x S c t : ℚ) : ℝ) ∧
      I.ubar S c t * ∏ d ∈ I.Dset S c t, (AtomicCSP.sigmaA x d)⁻¹ ≤
        (x c : ℝ) / 4 * ((I.qFormula x S c t : ℚ) : ℝ) *
          ∏ d ∈ I.Dset S c t, AtomicCSP.thetaA x d ∧
      I.ubar S c t / ((x c : ℝ) / 4 * ((I.qFormula x S c t : ℚ) : ℝ) *
        ∏ d ∈ I.Dset S c t, AtomicCSP.sigmaA x d) ≤ 1 ∧
      (I.sllData G x).LocalExact S c t (I.qFormula x S c t) := by sorry

end SamplingLLL
