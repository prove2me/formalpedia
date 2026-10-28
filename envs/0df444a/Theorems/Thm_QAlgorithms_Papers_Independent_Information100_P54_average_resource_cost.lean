-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P54_average_resource_cost
-- name    : QAlgorithms.Papers.Independent.Information100.P54.average_resource_cost
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:09:29.364977+00:00
-- url     : https://prove2.me/theorems/a7541298-0a73-4204-92e6-6d6417b76892
-- title:
--   Lemma 5 (Average resource cost)
-- statement:
--   Let $0<\eta<1$, $q=1-\eta$ and $s\ge1$ be an integer. Let $g(x)=((x+1)\ln(x+1)-x\ln x)/\ln2$, with $g(0)=0$. Write $d_{s,m}=\binom{s+m-1}{m}$, $c_\eta(x)=g(x)-g(qx)$, and define the resource cost by its explicit sector formula
--
--   $$F_{\eta,s}(m)=\log_2d_{s,m}-\mathbb E_{L\sim\operatorname{Bin}(m,q)}\log_2d_{s,L}.$$
--
--   For every integer $m\ge0$,
--
--   $$F_{\eta,s}(m)\le s c_\eta(m/s)+H(\operatorname{Bin}(m,q)).$$
--
--   For any nonnegative integer-valued random variable $M$ with finite mean, put $x=\mathbb EM/s$. Then
--
--   $$\mathbb EF_{\eta,s}(M)\le s c_\eta(x)+g(sqx).$$
--
--   Entropy and expected cost use nonnegative extended sums, so these inequalities also establish their finiteness. This replaces the sector label by a mean-energy bound. Lemma 4 identifies this explicit scalar cost with the REE of the constructed sector resource.
-- source:
--   Energy-constrained two-way capacities of pure-loss and quantum-limited amplifier channels, arXiv:2610.06832v1, PDF p. 14, Lemma 5 (Average resource cost)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54

noncomputable section

open scoped ENNReal Matrix

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P54

/-- arXiv:2610.06832v1, PDF pp.14–15, Lemma 5, Eqs.(B36)–(B37).
F is the explicit B15 scalar formula. Both expectations use nonnegative extended sums. -/
theorem average_resource_cost (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1)
    (s : ℕ) (hs : 1 ≤ s) :
    (∀ m : ℕ, ENNReal.ofReal (sectorCost eta s m) ≤
      ENNReal.ofReal ((s : ℝ) * lossRate eta ((m : ℝ) / s)) +
        ∑ ell ∈ Finset.range (m + 1), ENNReal.ofReal
          (-binomialMass m (1 - eta) ell * Real.log (binomialMass m (1 - eta) ell) /
            Real.log 2)) ∧
    (∀ p : PMF ℕ, countMean p ≠ ⊤ →
      averageSectorCost eta s p ≤ ENNReal.ofReal
        ((s : ℝ) * lossRate eta ((countMean p).toReal / s) +
          thermalEntropy ((1 - eta) * (countMean p).toReal))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P54

end
