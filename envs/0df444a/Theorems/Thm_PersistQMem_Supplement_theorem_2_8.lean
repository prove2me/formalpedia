-- Prove2me | Theorems.Thm_PersistQMem_Supplement_theorem_2_8
-- name    : PersistQMem.Supplement.theorem_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:17:49.14263+00:00
-- url     : https://prove2.me/theorems/56a77939-1ec0-4d51-bb50-59fc210999b3
-- title:
--   Theorem 2.8 — complete-Pauli specialization
-- statement:
--   Let $D=2^n\ge2$, let $\mathcal P_n^*$ be all $M=D^2-1$ nonidentity canonical Pauli operators with the uniform prior, and let $K\ge1$ with $q=\min(K,D)$. Then the structural quantities are exactly
--
--   $$
--   \beta=\frac1{D^2-1},\qquad
--   \zeta(K)=\frac{Dq-1}{D^2-1},\qquad
--   B_K=\frac{Dq+2K-3}{D^2-1}.
--   $$
--
--   Every persistent-memory receiver estimating all expectations with simultaneous signed error $0<\epsilon\le1/8$ and success probability at least $2/3$ for every state satisfies
--
--   $$
--   N\ge\frac{D^2-1}{20\epsilon^2(Dq+2K-3)}.
--   $$
--
--   If $1\le K\le D$, this implies the explicit absolute-constant bounds $N\ge(D-1)/(40K\epsilon^2)\ge D/(80K\epsilon^2)$.
--
--   Differences from the source:
--   - encoding: the unordered complete Pauli set → an arbitrary enumeration certified equivalent to all nonidentity canonical words; reason: ordering the same family changes neither the profile nor the task
--   - encoding: every receiver in the persistent-memory model → every achievable cap under the published protocol and a measurable real-vector terminal POVM density; reason: this unfolds the same universal operational claim using the source model's density representation
--   - reading: $\Omega(D/(K\epsilon^2))$ with an unspecified absolute constant → the consequences $(D-1)/(40K\epsilon^2)$ and $D/(80K\epsilon^2)$; reason: these explicit constants follow from the displayed exact bound for $D\ge2$ and $K\le D$
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), Theorem 2.8, (19), p.8 (PDF p.11)

import Mathlib
import Definitions.Def_PersistQMem_ProfileData
import Definitions.Def_PersistQMem_Supplement_Achievable
import Definitions.Def_PersistQMem_Supplement_IsWeightPauliFamily

set_option autoImplicit false

namespace PersistQMem
namespace Supplement

/-- **Theorem 2.8 (Complete-Pauli specialization), p.8** (Tao--Shen, *Structural Lower
Bounds for Quantum Property Estimation with Persistent Memory*, STOC 2027 submission,
manuscript of 2026-11-03, sha256 6d48ad24..., Theorem 2.8, (19), p.8, PDF p.11).

For all `D = 2^n >= 2`, the complete nonidentity canonical Pauli family with uniform prior has the
three exact profile values in (19).  Every successful persistent-memory receiver obeys the exact copy
lower bound.  When `K <= D`, the last two inequalities give an explicit absolute-constant form of the
paper's `Omega(D/(K epsilon^2))` clause.

**Formalization Note.** `G` is any enumeration of the exact canonical family, pinned by
`IsCompletePauliFamily`; `p` is `uniformPrior`.  The final asymptotic clause is rendered with the
absolute constants `1/40` and `1/80`, rather than an unquantified big-O predicate. -/
theorem theorem_2_8 (n K : Nat) (hn : 1 <= n) (hK : 1 <= K)
    (epsilon : Real) (he0 : 0 < epsilon) (he1 : epsilon <= 1 / 8)
    (G : Fin (completePauliCount n) -> Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) Complex)
    (hG : IsCompletePauliFamily n G) :
    let D := 2 ^ n
    let M := completePauliCount n
    let p := uniformPrior M
    let q := min K D
    gramNorm G p = 1 / ((D : Real) ^ 2 - 1) /\
    profile G p K = ((D : Real) * (q : Real) - 1) / ((D : Real) ^ 2 - 1) /\
    budget G p K =
      ((D : Real) * (q : Real) + 2 * (K : Real) - 3) / ((D : Real) ^ 2 - 1) /\
    (forall N : Nat, Achievable G K epsilon N ->
      ((D : Real) ^ 2 - 1) /
          (20 * epsilon ^ 2 * ((D : Real) * (q : Real) + 2 * (K : Real) - 3)) <=
        (N : Real)) /\
    (K <= D -> forall N : Nat, Achievable G K epsilon N ->
      ((D : Real) - 1) / (40 * (K : Real) * epsilon ^ 2) <= (N : Real) /\
      (D : Real) / (80 * (K : Real) * epsilon ^ 2) <= (N : Real)) := by sorry

end Supplement
end PersistQMem
