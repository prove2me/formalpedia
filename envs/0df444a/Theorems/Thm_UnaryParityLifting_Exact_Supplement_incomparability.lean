-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_Supplement_incomparability
-- name    : UnaryParityLifting.Exact.Supplement.incomparability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:51:46.186247+00:00
-- url     : https://prove2.me/theorems/201f8057-ca9d-4dc0-af0a-1aa8646d9f41
-- title:
--   Corollary 6.3 (= Theorem 1.2) — Incomparability with Resolution
-- statement:
--   Neither ordinary Resolution nor integer uSA(⊕) polynomially simulates the other. Polynomial simulation means one polynomial bound on target proof size in source proof size plus input encoding length, uniform over all finite source CNFs and source proofs.
--
--   For every fixed surjective 1-stifling gadget g on m≥1 bits, there exist one positive expansion constant η, positive C,c,δ,c_L,δ_L, natural K and a common threshold n₀≥2, and a family of connected cubic graphs G_n on 2(n+2) vertices with expansion at least η and odd total charges χ_n. Let H_n=SoD_(n²)∘g and let T_n be the graph Tseitin CNF of (G_n,χ_n). For all n≥n₀, both formulas have binary length at most C(n+1)^K, and all four entries hold:
--
--   $$\exists\pi_H:\ |\pi_H|\le C(n+1)^K,\qquad\forall q_H:\ s(q_H)\ge\exp(cn^\delta),$$
--   $$\forall\pi_T:\ |\pi_T|\ge\exp(cn),\qquad\exists q_T:\ s(q_T)\le C(n+1)^K.$$
--
--   The π's are actual Resolution refutations and the q's actual valid unary parity certificates. In addition, every q_H satisfies s(q_H)≥exp(c_L L_n^{δ_L}), where L_n=|H_n|. The graphs, their expansion and charges, and both upper-bound proofs are conclusions, with no supplied hard-family hypothesis. This single result includes the introduction's Theorem 1.2 and its explicit encoding-length clause.
--
--   Differences from the source:
--   - encoding: n-vertex cubic expander family on admissible even sizes → graphs on 2(n+2) vertices indexed by every natural n; reason: vertex count is Θ(n), excludes impossible odd cubic orders and leaves an unbounded family
--   - encoding: polynomial and exponential table entries and length lower bound → uniform explicit constants, a common threshold and fixed matched syntax; reason: all four cells, both length bounds, both non-simulations and the L_n clause are retained
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), printed/PDF p.19, Corollary 6.3; alias Theorem 1.2, printed/PDF p.3

import Definitions.Def_UnaryParityLifting_Exact_Supplement_sinkDAG
import Definitions.Def_UnaryParityLifting_Exact_Supplement_resolution
import Definitions.Def_UnaryParityLifting_Exact_Supplement_tseitin
import Definitions.Def_UnaryParityLifting_Exact_averaging

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

/-- Corollary 6.3 (= Theorem 1.2): both negations and both concrete witness families. -/
theorem incomparability :
    ¬ ResolutionSimulatesParity ∧ ¬ ParitySimulatesResolution ∧
    ∀ (m : ℕ) (g : (Fin m → Bool) → Bool), 1 ≤ m → Function.Surjective g →
      LiftSAParity.IsOneStifling g →
      ∃ ε C c δ cL δL : ℝ,
        0 < ε ∧ 0 < C ∧ 0 < c ∧ 0 < δ ∧ 0 < cL ∧ 0 < δL ∧
      ∃ K n₀ : ℕ, 2 ≤ n₀ ∧
      ∃ (G : (n : ℕ) → SimpleGraph (Fin (2 * (n + 2))))
        (χ : (n : ℕ) → Fin (2 * (n + 2)) → ZMod 2),
        (∀ n, (G n).Connected ∧ cubic (G n) ∧ Expands (G n) ε ∧ ∑ v, χ n v = 1) ∧
        ∀ n : ℕ, n₀ ≤ n →
          (liftedLength g n : ℝ) ≤ C * (n + 1 : ℝ) ^ K ∧
          (∃ p, Resolution (liftedSink g n) p ∧ (p.length : ℝ) ≤ C * (n + 1 : ℝ) ^ K) ∧
          (∀ q : CertificateSyntax (liftedSink g n), q.Valid →
            Real.exp (c * (n : ℝ) ^ δ) ≤ (chargedSize (binaryCharge _) q : ℝ) ∧
            Real.exp (cL * (liftedLength g n : ℝ) ^ δL) ≤ (chargedSize (binaryCharge _) q : ℝ)) ∧
          (cnfBits (tseitin (G n) (χ n)) : ℝ) ≤ C * (n + 1 : ℝ) ^ K ∧
          (∀ p, Resolution (tseitin (G n) (χ n)) p → Real.exp (c * n) ≤ (p.length : ℝ)) ∧
          (∃ q : CertificateSyntax (tseitin (G n) (χ n)), q.Valid ∧
            (chargedSize (binaryCharge _) q : ℝ) ≤ C * (n + 1 : ℝ) ^ K) := by sorry

end UnaryParityLifting.Exact.Supplement
