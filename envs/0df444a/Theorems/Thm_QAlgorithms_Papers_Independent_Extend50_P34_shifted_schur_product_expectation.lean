-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_shifted_schur_product_expectation
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.shifted_schur_product_expectation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:03:09.446147+00:00
-- url     : https://prove2.me/theorems/2ca75dfd-47d6-433c-968c-6a8c8cfc4e8a
-- title:
--   Lemma 4.8
-- statement:
--   Let $q$ be a distribution on $[d]$, and let $\mu\vdash r_1$, $\nu\vdash r_2$. For every $t$ between $\max(r_1,r_2)$ and $r_1+r_2$, choose arbitrary fixed sets $R_1,R_2\subseteq[t]$ of sizes $r_1,r_2$ whose union is $[t]$. Then
--
--   $$\mathbb E_{\lambda\sim\mathrm{SW}_q^n}[s_\mu^*(\lambda)s_\nu^*(\lambda)]=\sum_t C^t_{r_1r_2}n^{\downarrow t}\mathbb E_{w_1\sim S(R_1),w_2\sim S(R_2)}[\chi_\mu(w_1)\chi_\nu(w_2)p_{\bar w_1\bar w_2}(q)].$$
--
--   The permutations are independent uniform on the whole symmetric groups and are extended by fixing the complement. This computes generic shifted-Schur product moments; the value is independent of the allowed support choices. Here $C^t_{r_1r_2}=r_1!r_2!/[(t-r_1)!(t-r_2)!(r_1+r_2-t)!]$, and $p_\pi(q)$ is the product of power sums indexed by the full cycle type of $\pi$.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 37, Lemma 4.8

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Lemma 4.8, arXiv:1501.05028v1, PDF p.37. Whole symmetric groups, not fixed cycle classes. Empty partitions are included by the factorial expression C, which is 1 when r1=r2=t=0. -/
theorem shifted_schur_product_expectation
    (d n : ℕ) (hd : 0 < d) (q : Fin d → ℝ) (hq : Learning.IsDistribution q)
    (mu nu : YoungDiagram)
    (R1 R2 : (t : ℕ) → Finset (Fin t))
    (hR : ∀ t ∈ Finset.Icc (max mu.card nu.card) (mu.card+nu.card),
      (R1 t).card = mu.card ∧ (R2 t).card = nu.card ∧ R1 t ∪ R2 t = Finset.univ) :
    expect (n := n) q (fun lambda => shiftedSchur mu lambda * shiftedSchur nu lambda) =
      ∑ t ∈ Finset.Icc (max mu.card nu.card) (mu.card+nu.card),
        ((mu.card.factorial : ℝ)*nu.card.factorial /
          ((t-mu.card).factorial*(t-nu.card).factorial*(mu.card+nu.card-t).factorial : ℕ)) *
        falling n t * productCharacterMean q mu nu (R1 t) (R2 t) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
