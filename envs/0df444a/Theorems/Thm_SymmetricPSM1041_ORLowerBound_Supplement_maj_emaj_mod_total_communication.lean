-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_Supplement_maj_emaj_mod_total_communication
-- name    : SymmetricPSM1041.ORLowerBound.Supplement.maj_emaj_mod_total_communication
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:48:21.278641+00:00
-- url     : https://prove2.me/theorems/00aef9aa-69fc-474f-aece-5de4f5965db4
-- title:
--   Corollary 25 (= Theorem 2) — $\Omega(n\log n)$ for MAJ and EMAJ, $\Omega(n\log q)$ for MOD$_q$
-- statement:
--   Both of the following hold, for perfectly correct, support-private PSM protocols.
--
--   1. There are constants $C>0$ and $N\ge1$ such that for every $n\ge N$, for $f=\mathrm{MAJ}_n$ and for $f=\mathrm{EMAJ}_n$, every perfectly correct, support-private protocol $P$ for $f$ has an input $x$ and a seed $r$ with
--   $$\sum_{i=1}^n|M_i(x_i,r)|\ge C\,n\log_2 n.$$
--   2. For every fixed $c>0$ there are $C>0$ and $N\ge1$, depending only on $c$, such that for every $n\ge N$ and every integer $q$ with $2\le q\le(1-c)n$, every perfectly correct, support-private protocol $P$ for $\mathrm{MOD}_{q,n}$ has an input $x$ and a seed $r$ with
--   $$\sum_{i=1}^n|M_i(x_i,r)|\ge C\,n\log_2 q.$$
--
--   These are the operational statements $C(\mathrm{MAJ}_n),C(\mathrm{EMAJ}_n)=\Omega(n\log n)$ and $C(\mathrm{MOD}_q)=\Omega(n\log q)$, about the worst-case actual transcript length. They are the paper's Theorem 2, stated again as Corollary 25. Since perfect privacy implies support privacy, they also hold for perfect PSMs.
--
--   Differences from the source:
--   - encoding: parties indexed by [n]={1,…,n} → parties indexed by Fin n; reason: the bijection i↦i+1 preserves every input and coordinate subset
--   - encoding: arbitrary finite nonempty shared seed set R → Fin P.seedCount with positive unrestricted seedCount; reason: reindexing preserves uniform laws, supports and realized lengths
--   - encoding: C(f) = Ω(g) with C(f) = min over protocols of max_{x,r} |M(x,r)| → ∃ C > 0, ∃ N ≥ 1, ∀ n ≥ N (and ∀ q in range), every admissible protocol has x, r with transcript length ≥ C·g; reason: operational definition of C on p. 7 with the Ω constants uniform over protocols and over q; bounded q is included
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 3, Theorem 2; p. 18, Corollary 25 (derivation pp. 17–18)

import Mathlib
import Definitions.Def_SymmetricPSM1041_ORLowerBound_CostsRestrictions
import Definitions.Def_SymmetricPSM1041_ORLowerBound_Supplement_ExplicitFunctions

namespace SymmetricPSM1041.ORLowerBound.Supplement

theorem maj_emaj_mod_total_communication :
    (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ f : (Fin n → Bool) → Bool, (f = majFunction n ∨ f = emajFunction n) →
      ∀ P : PSM (Fin n), PerfectCorrect P f → SupportPrivate P f →
        ∃ (x : Fin n → Bool) (r : Fin P.seedCount),
          C * (n : ℝ) * Real.logb 2 n ≤ (transcriptLength P x r : ℝ)) ∧
    (∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ (1 - c) * n →
      ∀ P : PSM (Fin n), PerfectCorrect P (modFunction q n) →
        SupportPrivate P (modFunction q n) →
        ∃ (x : Fin n → Bool) (r : Fin P.seedCount),
          C * (n : ℝ) * Real.logb 2 q ≤ (transcriptLength P x r : ℝ)) := by sorry

end SymmetricPSM1041.ORLowerBound.Supplement
