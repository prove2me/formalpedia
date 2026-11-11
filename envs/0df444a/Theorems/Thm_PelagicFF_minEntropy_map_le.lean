-- Prove2me | Theorems.Thm_PelagicFF_minEntropy_map_le
-- name    : PelagicFF.minEntropy_map_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:09.29319+00:00
-- url     : https://prove2.me/theorems/89754fb5-7133-49df-80ad-d066913208c2
-- title:
--   §4.2.2, pp.30–31 — $V_\tau$ has at most $N$ preimages and raises $D_\infty$ by at most $n$
-- statement:
--   Let $N=2^n$, let $B\subseteq\{-1,1\}^N$ be a nonempty set of truth tables, let $y_\tau:B\to\{0,1\}^n$ be any map and $V(G)=G\odot\chi_{y_\tau(G)}$. Then:
--
--   1. every $v\in\{-1,1\}^N$ has at most $N$ preimages under $V$ in $B$;
--   2. for $G$ uniform on $B$, $\max_v\Pr[V(G)=v]\le N/|B|$;
--   3. $D_\infty(V(G))\le D_\infty(G)+n$.
--
--   In the lower bound $B=B_\tau$ is Bob's side of a transcript rectangle and $y_\tau$ his output function, so the pair $(F_\tau,V_\tau(G_\tau))$ keeps combined deficiency $c+2n$.
--
--   **Formalization Note** $y_\tau$ is given on all truth tables; only its values on $B$ matter.
--
--   Differences from the source:
--   - generalization: B_τ, Bob's side of a non-rare transcript rectangle → any nonempty set B of truth tables; reason: the argument uses only that G_τ is uniform on B_τ; B = B_τ gives the page's claim
--   - encoding: y_τ : B_τ → {0,1}ⁿ → a function on all truth tables, read only on B; reason: every function on B extends; same instances
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §4.2.2, pp.30–31

import Mathlib
import Definitions.Def_PelagicFF_PFF
import Definitions.Def_PelagicFF_maskByChar
import Definitions.Def_PelagicFF_minEntropyDeficiency

namespace PelagicFF

/-- **The min-entropy map bound (§4.2.2, pp.30–31).** Let `N = 2ⁿ`, let `B ⊆ {−1,1}^N` be a
nonempty set of truth tables, let `y_τ : B → {0,1}ⁿ` be any labelling and `V(G) = G ⊙ χ_{y_τ(G)}`.
Then every `v` has at most `N` preimages in `B`; for `G` uniform on `B`,
`max_v Pr[V(G) = v] ≤ N/|B|`; and `D∞(V(G)) ≤ D∞(G) + n`.

arXiv:2610.05585 (held version, sha256 4564aef3…), §4.2.2, pp.30–31: "We next show that applying
this function increases the min-entropy deficiency by at most n. That is, D∞(V_τ(G_τ)) ≤ D∞(G_τ) + n.
… Thus v has at most N pre-images under V_τ. Since G_τ is uniform on B_τ,
max_v Pr[V_τ(G_τ) = v] ≤ N/|B_τ|."

**Formalization Note.** Truth tables are `BoolFn n = (Fin n → Bool) → Bool` (`N = 2ⁿ` coordinates);
`y_τ` is given on all truth tables and only its values on `B` matter. -/
theorem minEntropy_map_le (n : ℕ) (B : Finset (BoolFn n)) (hB : B.Nonempty)
    (yτ : BoolFn n → (Fin n → Bool)) :
    (∀ v : BoolFn n, (B.filter (fun G => maskByChar G (yτ G) = v)).card ≤ 2 ^ n) ∧
    (∀ v : BoolFn n, ((PMF.uniformOfFinset B hB).map (fun G => maskByChar G (yτ G)) v).toReal ≤
      (2 : ℝ) ^ n / B.card) ∧
    minEntropyDeficiency ((PMF.uniformOfFinset B hB).map (fun G => maskByChar G (yτ G))) ≤
      minEntropyDeficiency (PMF.uniformOfFinset B hB) + n := by sorry

end PelagicFF
