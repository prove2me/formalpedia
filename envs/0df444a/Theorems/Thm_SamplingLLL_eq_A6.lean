-- Prove2me | Theorems.Thm_SamplingLLL_eq_A6
-- name    : SamplingLLL.eq_A6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:00:19.575189+00:00
-- url     : https://prove2.me/theorems/32eb9bd3-5dd1-4ae3-b9de-caf2096f4fac
-- title:
--   (A5), (A6), p.68 — response of the potential $h$
-- statement:
--   Under the hypotheses of Theorem 2.6, for a task $(S,c)$ with $c\notin S$, the response matrix (12) with $\bar a_t=u_t$ and the potential $h$ of (A2) satisfy
--   $$
--   (Mh)_i\le\frac{2B_c}{\sigma_c}\sum_tq_c(t)\Big(\prod_{d\in D_t}\theta_d\Big)\Big(\sum_{d\in D_t}h_d\Big)\le\frac{2B_c}{e\sigma_c}, \tag{A5}
--   $$
--   $$
--   h_c=\frac{x_c(2+x_c)}{8(1-x_c/4)(1-x_c/2)},\qquad\frac{2B_c}{\sigma_ch_c}=\frac{4-2x_c}{2+x_c}\le2,
--   $$
--   and $Mh\le\frac2eh$ (A6).
--
--   Differences from the source: none.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), eqs. (A5), (A6), p.68

import Mathlib
import Definitions.Def_SamplingLLL_sllAnalysis

set_option autoImplicit false

namespace SamplingLLL

/-- (A5), the formula for `h_c`, and (A6), p.68: for the response matrix (12) of Appendix G with
`ā_t = u_t`, `(Mh)_i ≤ (2B_c/σ_c) Σ_t q_c(t) (∏_{d∈D_t} θ_d) (Σ_{d∈D_t} h_d) ≤ 2B_c/(e σ_c)`, and `Mh ≤ (2/e) h`.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), eqs. (A5), (A6), p.68. -/
theorem eq_A6 {n m : ℕ} (I : AtomicCSP n m) (G : Finset (Fin m)) (x : Fin m → ℚ) (p : Fin m → ℝ)
    (hx : ∀ a, 0 < x a ∧ x a < 1) (hp : ∀ a, ((I.badProb a : ℚ) : ℝ) ≤ p a)
    (hG : ∀ a ∈ G, I.SamplingGood p a) (hSLL : I.SLL G p x)
    (S : Finset (Fin m)) (c : Fin m) (hc : c ∉ S) :
    let Bc : ℝ := (x c : ℝ) / 4
    let σc : ℝ := AtomicCSP.sigmaA x c
    let Mh : ℝ := ∑ j : Finset (Fin m) × Fin m,
      (I.sllData G x).respM I.ubar (S, c) j * AtomicCSP.hTask x j
    (Mh ≤ 2 * Bc / σc * ∑ t ∈ (I.sllData G x).leavesOf S c,
        ((I.qFormula x S c t : ℚ) : ℝ) * (∏ d ∈ I.Dset S c t, AtomicCSP.thetaA x d) *
          ∑ d ∈ I.Dset S c t, AtomicCSP.hA x d) ∧
    (2 * Bc / σc * ∑ t ∈ (I.sllData G x).leavesOf S c,
        ((I.qFormula x S c t : ℚ) : ℝ) * (∏ d ∈ I.Dset S c t, AtomicCSP.thetaA x d) *
          ∑ d ∈ I.Dset S c t, AtomicCSP.hA x d) ≤ 2 * Bc / (Real.exp 1 * σc) ∧
    AtomicCSP.hA x c =
      (x c : ℝ) * (2 + (x c : ℝ)) / (8 * (1 - (x c : ℝ) / 4) * (1 - (x c : ℝ) / 2)) ∧
    2 * Bc / (σc * AtomicCSP.hA x c) = (4 - 2 * (x c : ℝ)) / (2 + (x c : ℝ)) ∧
    (4 - 2 * (x c : ℝ)) / (2 + (x c : ℝ)) ≤ 2 ∧
    Mh ≤ 2 / Real.exp 1 * AtomicCSP.hA x c := by sorry

end SamplingLLL
