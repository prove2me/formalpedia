-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_Supplement_parity_lower_bound
-- name    : UnaryParityLifting.Exact.Supplement.parity_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:49:25.069307+00:00
-- url     : https://prove2.me/theorems/8b3e0e31-c211-4798-88dc-614908541cc6
-- title:
--   Corollary 6.2 — Unary parity-certificate lower bounds
-- statement:
--   Fix a surjective 1-stifling gadget g on m≥1 bits. Write N(n)=n⁴ceil(log₂(n²+1)) for the base bit count, H_n=SoD_(n²)∘g and L_n=|H_n| for its actual lifted binary length. There are fixed c,δ,c_L,ε>0, depending only on g, such that every integer uSA(⊕) certificate q of H_n, for every n≥1, has charged written size s(q) satisfying both
--
--   $$s(q)\ge 2^{cN(n)^\delta},\qquad s(q)\ge\exp(c_L L_n^\varepsilon).$$
--
--   All input monomial coefficients, parity-clause occurrences and unary magnitudes are charged. Constants precede n and every certificate. The finite positive prefix is included by reducing the constants; the lower bound is not silently restricted to an eventual subsequence. These bounds supply the hard entry of the Sink-of-DAG witness in incomparability.
--
--   Differences from the source:
--   - encoding: size and the exp(L_n^Ω(1)) formulation → fixed binary charge and explicit uniform positive constants in both inequalities; reason: the source size convention and full family range are retained, including the finite positive prefix
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), printed/PDF p.19, Corollary 6.2

import Definitions.Def_UnaryParityLifting_Exact_Supplement_sinkDAG
import Definitions.Def_UnaryParityLifting_Exact_averaging

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

/-- Corollary 6.2, with the finite positive prefix included and actual encoding length. -/
theorem parity_lower_bound {m : ℕ} (g : (Fin m → Bool) → Bool)
    (hm : 1 ≤ m) (hg : Function.Surjective g) (hs : LiftSAParity.IsOneStifling g) :
    ∃ c δ cL ε : ℝ, 0 < c ∧ 0 < δ ∧ 0 < cL ∧ 0 < ε ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ q : CertificateSyntax (liftedSink g n), q.Valid →
        (2 : ℝ) ^ (c * (baseVariables n : ℝ) ^ δ) ≤
          (chargedSize (binaryCharge _) q : ℝ) ∧
        Real.exp (cL * (liftedLength g n : ℝ) ^ ε) ≤
          (chargedSize (binaryCharge _) q : ℝ) := by sorry

end UnaryParityLifting.Exact.Supplement
