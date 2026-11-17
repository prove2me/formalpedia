-- Prove2me | Theorems.Thm_PersistQMem_Supplement_theorem_2_5
-- name    : PersistQMem.Supplement.theorem_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:16:17.077287+00:00
-- url     : https://prove2.me/theorems/583a0a35-f1e1-456c-bec0-8c12f4e6615d
-- title:
--   Theorem 2.5 — finite Pauli copy bounds
-- statement:
--   Let $n\ge2$, $1\le w\le n$, $K\ge1$, and $0<\epsilon\le1/8$. Request all $M=3^w\binom nw$ canonical weight-$w$ Pauli means simultaneously. For every integer $p\ge1$ with $2p\ge w$, define
--
--   $$
--   B_{n,w,K}(p)=\min\!\left\{1,\frac{K^{w/(2p)}(n+\sqrt{8np})^w}{Mw!}\right\}+\frac{2K-2}{M}.
--   $$
--
--   Every successful persistent-memory receiver with worst-case copy cap $N$ satisfies
--
--   $$
--   \frac{1}{20\epsilon^2B_{n,w,K}(p)}\le N.
--   $$
--
--   Conversely, the cap
--
--   $$
--   \left\lceil\frac{13}{6}\,3^w\epsilon^{-2}\ln(6M)\right\rceil
--   $$
--
--   is achievable with retained quantum dimension one, and hence under any cap $K\ge1$. The lower bound holds for every legal $p$.
--
--   Differences from the source:
--   - encoding: the least worst-case budget $N^*$ and its two inequalities → every achievable cap is lower-bounded and the displayed cap is explicitly achievable; reason: this is equivalent on the finite Pauli task and avoids a default value for an empty infimum
--   - encoding: an arbitrary final measurement producing a real output vector → a jointly measurable POVM density on the same real-vector output space against an s-finite reference kernel; reason: this is the measurable density representation used by the published protocol model and changes no receiver instance
--   - encoding: the set $\mathcal P_{n,w}$ → an arbitrary enumeration certified equivalent to the canonical weight-$w$ labels; reason: ordering the same finite family changes no task instance
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), Theorem 2.5, (9)–(10), pp.5–6 (PDF pp.8–9)

import Mathlib
import Definitions.Def_PersistQMem_Supplement_Achievable
import Definitions.Def_PersistQMem_Supplement_IsWeightPauliFamily

set_option autoImplicit false

namespace PersistQMem
namespace Supplement

/-- **Theorem 2.5 (Finite Pauli copy bounds), pp.5--6** (Tao--Shen, *Structural
Lower Bounds for Quantum Property Estimation with Persistent Memory*, STOC 2027 submission,
manuscript of 2026-11-03, sha256 6d48ad24..., Theorem 2.5, (9)--(10), pp.5--6,
PDF pp.8--9).

For `n >= 2`, `1 <= w <= n`, `K >= 1`, `0 < epsilon <= 1/8`, and every integer
`p >= 1` with `2p >= w`, put
`M = 3^w binom(n,w)` and
`B = min{1, K^(w/(2p)) (n + sqrt(8np))^w / (M w!)} + (2K-2)/M`.
Every successful persistent-`K` receiver with copy cap `N` has
`1/(20 epsilon^2 B) <= N`, while the displayed ceiling is achievable with retained dimension
one (and hence also under cap `K`).

**Formalization Note.** Instead of taking a potentially default-valued infimum called `N*`, the two
budget inequalities are stated operationally: every achievable cap obeys the lower bound, and the
upper cap is explicitly achievable.  `IsWeightPauliFamily` supplies an enumeration of exactly the
canonical Hermitian strings.  The fractional power is `Real.rpow`. -/
theorem theorem_2_5 (n w K : Nat) (hn : 2 <= n) (hw0 : 1 <= w) (hwn : w <= n)
    (hK : 1 <= K) (epsilon : Real) (he0 : 0 < epsilon) (he1 : epsilon <= 1 / 8)
    (p : Nat) (hp0 : 1 <= p) (hpw : w <= 2 * p)
    (G : Fin (weightPauliCount n w) -> Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) Complex)
    (hG : IsWeightPauliFamily n w G) :
    let M := weightPauliCount n w
    let B := min 1
        (Real.rpow (K : Real) ((w : Real) / (2 * (p : Real))) *
          ((n : Real) + Real.sqrt (8 * (n : Real) * (p : Real))) ^ w /
          ((M : Real) * (Nat.factorial w : Real))) +
        (2 * (K : Real) - 2) / (M : Real)
    let U := ⌈(13 / 6 : Real) * (3 : Real) ^ w * epsilon⁻¹ ^ 2 *
      Real.log (6 * (M : Real))⌉₊
    (forall N, Achievable G K epsilon N ->
      1 / (20 * epsilon ^ 2 * B) <= (N : Real)) /\
    Achievable G K epsilon U /\ Achievable G 1 epsilon U := by sorry

end Supplement
end PersistQMem
