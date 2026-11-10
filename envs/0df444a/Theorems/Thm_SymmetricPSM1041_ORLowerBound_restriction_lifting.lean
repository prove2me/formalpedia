-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_restriction_lifting
-- name    : SymmetricPSM1041.ORLowerBound.restriction_lifting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:57:45.68134+00:00
-- url     : https://prove2.me/theorems/87e8098e-8b54-4aac-97b0-2f45e8ac9957
-- title:
--   Lemma 6 — exact restriction lifting for both privacy classes
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ be any Boolean function. Fix one privacy class $\rho$, either perfect privacy or support privacy, and integers $1\le s\le n$ and $B\ge0$. Suppose that for every coordinate set $I\subseteq[n]$ of size at least $s$, some full assignment $z$ satisfies $C_{\rm indiv}^{\rho}(f_{I,z})\ge B+1$. Then every perfectly correct protocol $P$ for $f$ in that same class has an input and seed with
--
--   $$\ell_P(x,r)\ge (B+1)(n-s+1).$$
--
--   The individual-complexity hypothesis means that every admissible protocol for the restriction has some party with actual alphabet cardinality at least $2^{B+1}$; equivalently, there is no protocol whose every local alphabet has size at most $2^{B+1}-1$. This is exactly the base-two logarithmic bound, not a bound on one chosen protocol. The conclusion is the operational meaning of $C^{\rho}(f)\ge(B+1)(n-s+1)$.
--
--   The same privacy parameter is used in the restricted hypotheses and the original conclusion. Every eligible free set is nonempty, and all coordinate subsets of sufficient size are included. This lemma links local alphabet obstructions to actual total bit lengths.
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: arbitrary finite nonempty shared seed set R → Fin P.seedCount with positive unrestricted seedCount; reason: reindexing preserves uniform laws, supports and realized lengths
--   - encoding: C_indiv of a restriction is at least B+1 → every admissible restricted protocol has a party with at least 2^(B+1) actually used messages; reason: base-two logarithm is monotone on positive alphabet sizes; unused declared symbols can be trimmed
--   - encoding: C(f)≥(B+1)(n−s+1) → every admissible P has a realized transcript meeting that exact bound; reason: this is the source’s operational definition on p. 7
--   - encoding: a restricted input in {0,1}^|I| → an input indexed by the subtype I; reason: a bijection to Fin |I| transports every restricted protocol without changing costs or privacy
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 8, Lemma 6 (proof pp. 8–9)

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions

namespace SymmetricPSM1041.ORLowerBound

theorem restriction_lifting {n : ℕ} (f : (Fin n → Bool) → Bool)
    (ρ : PrivacyClass) (s B : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hrestr : ∀ I : Finset (Fin n), s ≤ I.card → ∃ z : Fin n → Bool,
      IndividualLowerBound ρ (restrictFunction f I z) (B + 1)) :
    ∀ P : PSM (Fin n), PerfectCorrect P f → HasPrivacy ρ P f →
      ∃ (x : Fin n → Bool) (r : Fin P.seedCount),
        (B + 1) * (n - s + 1) ≤ transcriptLength P x r := by sorry

end SymmetricPSM1041.ORLowerBound
