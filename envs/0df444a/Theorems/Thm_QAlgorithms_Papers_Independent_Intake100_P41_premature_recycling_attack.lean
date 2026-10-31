-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P41_premature_recycling_attack
-- name    : QAlgorithms.Papers.Independent.Intake100.P41.premature_recycling_attack
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:22:56.365821+00:00
-- url     : https://prove2.me/theorems/166bf6c2-0bd3-478d-a2cb-3e83e4eb0c42
-- title:
--   Certain forgery after premature hash-key disclosure
-- statement:
--   Let $K$ be a finite nonempty hash-key set, let $T=\{0,1\}^m$, and let $h:K\times X\to T$ be any hash family. Fix distinct messages $x,x'\in X$. Suppose Alice exports the hash key before Bob stops accepting the pending message. Consider an allowed subsequent use that reveals that key to Eve while the intercepted pair $(x,h_k(x)\oplus p)$ remains pending.
--
--   There is an attack depending only on the disclosed $k$ and intercepted pair, and not on the pad $p$, such that
--
--   $$
--   \Pr_{k,p}[\text{Bob accepts the substituted message }x']=1,
--   $$
--
--   where $k$ and $p$ are independent and uniform. The known-key context supplies the key before the attack chooses its pair, and Bob then executes the ordinary verification rule. No AXU property is required. This witness explains why arbitrary reuse must wait until pending verification has closed; it does not assert that every subsequent application reveals the key.
-- source:
--   Key recycling in authentication, arXiv:1202.1229v3, PDF p. 10, Section 4 opening; Section 1.2 on p.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P41

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P41

open QAlgorithms.Papers.Independent.Bridge50.P44 (xorWord verifyTag)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3,10: in the allowed context that discloses a prematurely exported
hash key, there is a substitution accepted with probability one before Bob's
pending verification closes. The attacker never receives the OTP. No AXU
assumption is needed, and the result concerns this premature-release context. -/
theorem premature_recycling_attack {K X : Type*} [Fintype K] [Nonempty K]
    {m : ℕ} (h : K → X → Tag m) (x xprime : X) (hne : x ≠ xprime) :
    ∃ a : K → X × Tag m → X × Tag m,
      uniformProbability (fun seed : K × Tag m =>
        let view := (prematureReleaseView h a seed.1 seed.2 x).2
        view.submitted.1 = xprime ∧ view.accepted = true) = 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P41

end
