-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_Supplement_size_degree_lifting
-- name    : UnaryParityLifting.Exact.Supplement.size_degree_lifting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:52:31.988753+00:00
-- url     : https://prove2.me/theorems/3ea1d0f3-5100-424c-9c50-246c61e617b2
-- title:
--   Corollary 4.4 — Exact real size–degree lifting
-- statement:
--   Fix a surjective 1-stifling gadget g on m≥1 bits. Uniformly for all N,S≥1, positive width bounds w, source CNFs F on N variables with width≤w, and input unary parity certificates of the unchanged published charged size at most S for F∘g, set T=(mN+2)S and
--
--   $$R=\min\{N,\max\{w,\lceil c_g^{-1}\log_2(2T)\rceil\}\},$$
--
--   where c_g is exactly (3.3). There is an exact formal real SA certificate q with nonnegative constant axiom multipliers, nonnegative collected term weights, degree≤R and
--
--   $$W(q)\le6T2^R.$$
--
--   Moreover there are C_d,C_m>0 and a natural K depending only on g, chosen before F,N,w,S and the input charge, such that R≤C_d(w+log(NS+1)) and W(q)≤C_m((N+1)2^w(S+1))^K. The full-degree R=N case requires no small-error assumption; empty clauses remain allowed. This is support for integer lifting, not an additional support for the frozen goal.
--
--   Differences from the source:
--   - encoding: integer ceiling and O_g/poly_g notation → natural ceiling in the positive domain and explicit constants uniform in all input data; reason: the ceilings agree here and the polynomial envelope expresses the same dependence on N, 2^w and S
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), printed/PDF p.15, Corollary 4.4

import Definitions.Def_UnaryParityLifting_Exact_Supplement_integerOutput

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

/-- Corollary 4.4, both branches of the cap and both uniform asymptotic consequences. -/
theorem size_degree_lifting {m : ℕ} (g : (Fin m → Bool) → Bool)
    (hm : 1 ≤ m) (hg : Function.Surjective g) (hs : LiftSAParity.IsOneStifling g) :
    ∃ Cd Cm : ℝ, 0 < Cd ∧ 0 < Cm ∧ ∃ K : ℕ,
    ∀ (N w S : ℕ) (F : LiftSAParity.CNF (Fin N))
      (enc : EncodingCharge (Fin N × Fin m)),
      1 ≤ N → 1 ≤ S → WidthAtMost F w →
      HasParityCertificate (LiftSAParity.lift F g) enc S →
      let R := liftingDegree g N w S
      let T := normalizationBudget m N S
      (R : ℝ) ≤ Cd * (w + Real.log (N * S + 1 : ℝ)) ∧
      ∃ q : RealCertificate F, q.IsExact ∧ q.DegreeLE R ∧
        q.mass ≤ 6 * T * (2 : ℝ) ^ R ∧
        q.mass ≤ Cm * ((N + 1 : ℝ) * (2 : ℝ) ^ w * (S + 1 : ℝ)) ^ K := by sorry

end UnaryParityLifting.Exact.Supplement
