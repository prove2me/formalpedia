-- Prove2me | Theorems.Thm_RecoveryStorage3SUM_Adaptive_lemma_2_1
-- name    : RecoveryStorage3SUM.Adaptive.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:50.60703+00:00
-- url     : https://prove2.me/theorems/c4483b6f-54d9-4961-b2d6-887a993da173
-- title:
--   Lemma 2.1 — residue-class counts of $A+B$ in $O(n+p\log p)$ word operations
-- statement:
--   Let $A,B$ be sets of at most $n$ integers and let $p\ge1$ be a modulus, all bounded by $H(n+2)^\kappa$. One word-RAM program, with word width $O(\log n)$, computes all $p$ residue-class counts
--   $$\mathrm{cong}(r)=|\{(a,b)\in A\times B:a+b\equiv_p r\}|,\qquad r\in[p],$$
--   within $C(n+p\log(p+1))$ steps on every coin sequence, leaving $\mathrm{cong}(r)$ in cell $r$.
--
--   The query procedure uses these counts for every run, which is what makes the overcount $\mathrm{cong}(c\bmod p)$ available for every target at once.
--
--   Differences from the source:
--   - encoding: $O(n+p\log p)$ → $C(n+p\log(p+1))$; reason: $\log(p+1)$ handles $p=1$, including the empty input, and gives the same asymptotic class for $p\ge2$
--   - encoding: a modulus $p$ → $1\le p\le H(n+2)^\kappa$; reason: the modulus and the array of p output addresses must fit the source word RAM; an arbitrary polynomial address bound is fixed before the instance
--   - encoding: integers bounded by $n^{O(1)}$ (standing assumption, §2) → $|x|\le H(n+2)^\kappa$ with $H,\kappa$ fixed first; reason: same class of inputs; constants are chosen after them
-- source:
--   Amir Carmel, Yakov Kosoburd, Robert Krauthgamer, STOC 2027 submission #561 (October 2026), Lemma 2.1, p.6

import Mathlib
import Definitions.Def_MatroidSensOracle_WordRAM
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Protocol
import Definitions.Def_RecoveryStorage3SUM_Adaptive_Construction

set_option autoImplicit false

namespace RecoveryStorage3SUM.Adaptive

open MatroidSensOracle in
/-- Lemma 2.1, p.6: the `p` residue-class counts of `A + B mod p` are computed in `O(n + p log p)` word
operations. The machine reads `p, |A|, |B|`, then `A`, then `B`; on halting, cell `r` holds `cong(r)`
for each `r ∈ [p]`. The bound uses `log (p + 1)`, which differs from `log p` only at `p = 1`. -/
theorem lemma_2_1 (H κ : ℕ) :
    ∃ (b : ℕ) (P : List Instr) (C : ℝ), 0 < b ∧ 0 < C ∧
      ∀ (n p : ℕ) (as bs : List ℤ), 1 ≤ p → (p : ℤ) ≤ (H : ℤ) * ((n : ℤ) + 2) ^ κ →
        as.Nodup → bs.Nodup → as.length ≤ n → bs.length ≤ n →
        (∀ a ∈ as, PolyBounded H κ n a) → (∀ b' ∈ bs, PolyBounded H κ n b') →
        ∀ ω : Coins, ∃ m,
          exec P ω ⌈C * ((n : ℝ) + (p : ℝ) * Real.log ((p : ℝ) + 1))⌉₊ 0 0
              (loadWords (wordWidth b n)
                ((p : ℤ) :: (as.length : ℤ) :: (bs.length : ℤ) :: (as ++ bs))) = some m ∧
            ∀ r < p, (m (r : ℤ)).toNat = congCount as.toFinset bs.toFinset p r := by sorry

end RecoveryStorage3SUM.Adaptive
