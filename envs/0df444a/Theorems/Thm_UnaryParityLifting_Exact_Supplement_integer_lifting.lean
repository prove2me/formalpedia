-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_Supplement_integer_lifting
-- name    : UnaryParityLifting.Exact.Supplement.integer_lifting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:53:33.530757+00:00
-- url     : https://prove2.me/theorems/10200356-df7d-43a8-b678-71ea84f370a5
-- title:
--   Theorem A.2 — Lifting to integer unary Sherali–Adams
-- statement:
--   Fix a surjective 1-stifling gadget g on m≥1 bits, with c_g exactly (3.3). For every source CNF F on N≥1 variables with positive width bound w and every input uSA(⊕) certificate for F∘g of published charged size at most S≥1, put T=(mN+2)S and choose the exact R of (4.7). There exists an exact integer uSA refutation q of F with degree≤R and nonnegative constant axiom multipliers. With
--
--   $$T_{N,R}=\sum_{j=0}^{\min(R,N)}2^j\binom Nj,$$
--
--   its coefficient mass satisfies
--
--   $$W(q)\le3\cdot4^R(S+T_{N,R})(6T2^R+1).$$
--
--   Both its mass and its total unary encoding size are bounded by C S^K(N+1)^{KR}, and R≤C_d(w+log(NS+1)), for positive C,C_d and a natural K depending only on g and chosen before all instance data. Unary size includes the actual listing of each used clause and term, variable indices and unary coefficients. All conclusions hold together for the same q, including the capped R=N case and formulas containing an empty clause. This gives the paper's integer output with its separate, larger mass bound.
--
--   Differences from the source:
--   - encoding: integer output, equation (4.7), and the two O-notation conclusions → integrality of the unchanged real-certificate data, natural ceiling, fixed unary listing cost and uniform polynomial constants; reason: this changes no instance, keeps every factor of (A.2), and expresses both mass and total encoding size for the same certificate
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), printed/PDF p.25, Theorem A.2

import Definitions.Def_UnaryParityLifting_Exact_Supplement_integerOutput

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

/-- Theorem A.2: explicit integer bound, unary size and degree asymptotics together. -/
theorem integer_lifting {m : ℕ} (g : (Fin m → Bool) → Bool)
    (hm : 1 ≤ m) (hg : Function.Surjective g) (hs : LiftSAParity.IsOneStifling g) :
    ∃ C Cd : ℝ, 0 < C ∧ 0 < Cd ∧ ∃ K : ℕ,
    ∀ (N w S : ℕ) (F : LiftSAParity.CNF (Fin N))
      (enc : EncodingCharge (Fin N × Fin m)),
      1 ≤ N → 1 ≤ S → WidthAtMost F w →
      HasParityCertificate (LiftSAParity.lift F g) enc S →
      let R := liftingDegree g N w S
      let T := normalizationBudget m N S
      (R : ℝ) ≤ Cd * (w + Real.log (N * S + 1 : ℝ)) ∧
      ∃ q : RealCertificate F, q.IsExact ∧ IntegerOutput q ∧ q.DegreeLE R ∧
        q.mass ≤ 3 * (4 : ℝ) ^ R * (S + termCount N R) * (6 * T * (2 : ℝ) ^ R + 1) ∧
        q.mass ≤ C * (S : ℝ) ^ K * (N + 1 : ℝ) ^ (K * R) ∧
        unaryOutputSize q ≤ C * (S : ℝ) ^ K * (N + 1 : ℝ) ^ (K * R) := by sorry

end UnaryParityLifting.Exact.Supplement
