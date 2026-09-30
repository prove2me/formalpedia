-- Prove2me | Theorems.Thm_SupplyChainTheory_wholesale_supplier_unimodal
-- name    : SupplyChainTheory.wholesale_supplier_unimodal
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:28:31.745053+00:00
-- url     : https://prove2.me/theorems/8e2abbc1-8765-4ce5-9236-85dfc0d92100
-- title:
--   Theorem 14.3: for IGFR demand the supplier's induced profit $\pi_s(Q, w(Q))$ is unimodal
-- statement:
--   **Theorem 14.3.** Suppose the demand has a density $f$, continuous on $[0, \infty)$ and positive on $(0, \infty)$,
--   with the increasing generalized failure rate (IGFR) property: $Q f(Q)/\bar F(Q)$ is
--   nondecreasing for $Q > 0$. When the supplier chooses the wholesale price $w(Q)$ of (14.14) that
--   induces the retailer to order $Q$, her profit $\pi_s(Q, w(Q))$ is unimodal on $Q \ge 0$: there
--   is a $Q^* > 0$ such that it is strictly increasing on $[0, Q^*]$ and strictly decreasing on
--   $[Q^*, \infty)$, and so has a unique maximum.
--
--   The book's proof computes the derivative (14.16),
--   $(r - v + p_r)\bar F(Q)\big(1 + \tfrac{p_s}{r - v + p_r} - \tfrac{Qf(Q)}{\bar F(Q)}\big) - (c - v)$:
--   positive near $0$, eventually negative, with the bracket decreasing by IGFR, so the derivative
--   changes sign once. Normal, exponential and gamma demands are IGFR. Positivity near $0$ needs
--   the chain optimum to be positive, $\bar F(0) > (c - v)/(r - v + p)$, automatic for nonnegative
--   demand.
--
--   **Formalization Note** The density enters as `volume.withDensity`; its positivity on
--   $(0, \infty)$ is what makes $\bar F$ strictly decreasing there, which the book uses.
--   Continuity is required on $[0, \infty)$ only, where the derivative (14.16) is taken. Global
--   continuity would exclude the exponential law, whose density jumps at $0$, and the book names
--   it as IGFR.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 571, Sect. 14.5, Theorem 14.3 and its proof, Eq. (14.16)-(14.17); after Lariviere and Porteus (2001)

import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem wholesale_supplier_unimodal (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    (hD : MeasureTheory.Integrable (fun x => x) D) (f : ℝ → ℝ)
    (hdens : D = MeasureTheory.volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hf : ContinuousOn f (Set.Ici 0)) (hfpos : ∀ x, 0 < x → 0 < f x) (hIGFR : IGFR f D)
    (hQ0 : (P.c - P.v) / (P.r - P.v + P.p) < 1 - ProbabilityTheory.cdf D 0) :
    ∃ Qs, 0 < Qs ∧ StrictMonoOn (supplierInducedProfit P D) (Set.Icc 0 Qs)
      ∧ StrictAntiOn (supplierInducedProfit P D) (Set.Ici Qs) := by sorry

end SupplyChainTheory
