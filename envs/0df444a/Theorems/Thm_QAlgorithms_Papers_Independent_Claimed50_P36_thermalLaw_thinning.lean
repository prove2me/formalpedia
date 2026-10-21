-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P36_thermalLaw_thinning
-- name    : QAlgorithms.Papers.Independent.Claimed50.P36.thermalLaw_thinning
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:33:20.604879+00:00
-- url     : https://prove2.me/theorems/20166158-4caf-493d-b3f9-a6a951d7a12a
-- title:
--   Photon loss preserves the Bose-Einstein law
-- statement:
--   For $m\ge0$ let $p_m(n)=(1+m)^{-1}(m/(1+m))^n$ be the Bose-Einstein number law, and let $\eta\in[0,1]$ be photon survival probability in the binomial loss kernel $W_\eta(y\mid n)$. For every $y\in\mathbb N$,
--
--   $$
--   \sum_{n=0}^{\infty}p_m(n)W_\eta(y\mid n)=p_{\eta m}(y).
--   $$
--
--   The series converges to the stated value, including complete loss, no loss, and the vacuum input. Thus geometric photon statistics remain geometric under thinning; this does not identify an optimizer for the lossy capacity.
-- source:
--   Information capacity formula of quantum optical channels, arXiv:quant-ph/0105042v1, PDF p. 15, Sentence following Eq.(63)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P36

open Filter

open scoped Topology ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable

-- Reuse the pinned accepted entropy definitions, preserving their codomains
-- and units. P24.bosonicEntropy is in bits: multiply by log 2 for nats.
-- P01.binaryEntropy is in nats and ENNReal-valued: use toReal only at the
-- finite binary-probability argument of binaryValue below.

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

/-- PDF p.15, unnumbered sentence after (63): Bose-Einstein input is taken to
Bose-Einstein output with mean eta*m. Includes eta=0, eta=1, and m=0. -/
theorem thermalLaw_thinning (eta m : ℝ)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (hm : 0 ≤ m) :
    ∀ y : ℕ, HasSum (fun n => thermalLaw m n * lossTransition eta n y)
      (thermalLaw (eta * m) y) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P36

end
