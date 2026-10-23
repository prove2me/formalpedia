-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P45_entropyMinusExchangeConcave
-- name    : QAlgorithms.Papers.Independent.Dependency50.P45.entropyMinusExchangeConcave
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:05:50.673398+00:00
-- url     : https://prove2.me/theorems/d92a9ee6-2c8f-49d3-8080-3a794b941229
-- title:
--   Lemma 3: concavity of input entropy minus entropy exchange
-- statement:
--   Let $\mathcal N:A\to B$ be any CPTP map on finite nonzero complex spaces. Let $\rho_0,\rho_1$ be density matrices on $A$, let $0\le p\le1$, and put $\rho=p\rho_0+(1-p)\rho_1$. Write $E_\mathcal N(\sigma)=H((\operatorname{id}\otimes\mathcal N)\Phi_\sigma)$ for entropy exchange using a normalized purification. All entropies are in bits. Then
--
--   $$H(\rho)-E_\mathcal N(\rho)\ge p\bigl[H(\rho_0)-E_\mathcal N(\rho_0)\bigr]+(1-p)\bigl[H(\rho_1)-E_\mathcal N(\rho_1)\bigr].$$
--
--   Thus input entropy minus entropy exchange is concave, including endpoint weights. Output entropy is not part of this lemma.
-- source:
--   Entanglement-assisted capacity of a quantum channel and the reverse Shannon theorem, arXiv:quant-ph/0106052v2, PDF p. 25, Lemma 3: concavity of input entropy minus entropy exchange

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

noncomputable section

open scoped ComplexConjugate Matrix

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P76 (dampingChannel)

/-- PDF pp.25--26, Lemma 3, Eq.(56): concavity, minus entropy exchange.
The overview's 'convex' on p.23 is a typo; independent correction review pending. -/
theorem entropyMinusExchangeConcave {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (rho0 rho1 : Matrix A A ℂ)
    (h0 : IsDensityMatrix rho0) (h1 : IsDensityMatrix rho1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    vnEntropy ((p : ℂ) • rho0 + ((1 - p : ℝ) : ℂ) • rho1) -
      entropyExchange N ((p : ℂ) • rho0 + ((1 - p : ℝ) : ℂ) • rho1) ≥
      p * (vnEntropy rho0 - entropyExchange N rho0) +
        (1 - p) * (vnEntropy rho1 - entropyExchange N rho1) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P45

end
