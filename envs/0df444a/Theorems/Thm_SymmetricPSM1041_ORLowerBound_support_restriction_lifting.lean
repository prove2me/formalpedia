-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_support_restriction_lifting
-- name    : SymmetricPSM1041.ORLowerBound.support_restriction_lifting
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T14:53:42.467447+00:00
-- url     : https://prove2.me/theorems/cde20291-14d7-4dc1-a639-d78cf4d9e18d
-- title:
--   Lemma 6 (support-privacy specialization) — lifting to total bit length
-- statement:
--   This is the support-privacy specialization of Lemma 6. Let $f:\{0,1\}^n\to\{0,1\}$ and let $1\le s\le n$ and $B\ge0$. Suppose that for every coordinate set $I\subseteq[n]$ with $|I|\ge s$, some fixing $z$ of the other coordinates makes every perfectly correct, support-private protocol for the restricted function use at least $2^{B+1}$ actual messages at some party. Then every perfectly correct, support-private protocol $P$ for $f$ has an input and seed with
--
--   $$
--   \ell_P(x,r)\ge(B+1)(n-s+1).
--   $$
--
--   The statement isolates the privacy class used by the mission goal while retaining the exact hypotheses, coefficient, arbitrary restrictions, and actual variable-length transcript cost of the source lemma. It is reusable whenever only support privacy is required.
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), pp. 8–9, Lemma 6, specialized to support privacy

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions

namespace SymmetricPSM1041.ORLowerBound

theorem support_restriction_lifting {n : ℕ} (f : (Fin n → Bool) → Bool)
    (s B : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hrestr : ∀ I : Finset (Fin n), s ≤ I.card → ∃ z : Fin n → Bool,
      IndividualLowerBound .support (restrictFunction f I z) (B + 1)) :
    ∀ P : PSM (Fin n), PerfectCorrect P f → SupportPrivate P f →
      ∃ (x : Fin n → Bool) (r : Fin P.seedCount),
        (B + 1) * (n - s + 1) ≤ transcriptLength P x r := by sorry

end SymmetricPSM1041.ORLowerBound
