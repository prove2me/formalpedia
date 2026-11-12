-- Prove2me | Theorems.Thm_SuccinctArgOWF_Kilian_hr_binding
-- name    : SuccinctArgOWF.Kilian.hr_binding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:49.605058+00:00
-- url     : https://prove2.me/theorems/78bebc5e-f44e-461d-8728-bf9427dc0211
-- title:
--   Lemma 4.3 — binding of interactive hashing [HR14, Theorem 3.7]
-- statement:
--   Let $H$ be an efficient family of pairwise-independent hash functions from $\{0,1\}^w$ to $\{0,1\}^{v}$, $v=v(w)\ge1$, and let $\ell=\ell(w)\ge1$ be polynomially bounded and polynomial-time computable. Consider Construction 4.2 with $\ell$ rounds and the family $H$ on inputs $y\in\{0,1\}^w$.
--
--   There exist a polynomial $p$, a constant $c>0$ and one oracle machine $A'$ such that for every $w$, every algorithm $A$ playing the role of $S$, every nonempty $L\subseteq\{0,1\}^w$ and every relation $W\subseteq\{0,1\}^*\times L$:
--
--   1. counting each oracle call as one step, $A'^A$ runs in time at most $p(w)\cdot2^{v}$;
--   2. writing $W_y=\{x:(x,y)\in W\}$,
--
--   $$\Pr_{y\leftarrow L}\bigl[A'^A(y)\in W_y\bigr]\;\ge\;\frac{c\,\varepsilon_A^2}{2^{10v}\,w^8}\cdot\min\Bigl\{1,\frac{2^{v\ell}}{|L|}\Bigr\},$$
--
--   where $\varepsilon_A$ is the probability that, after interacting with $R$, $A$ outputs $((x_0,y_0),(x_1,y_1))$ with $y_0\neq y_1$ in $L$, $(x_0,y_0),(x_1,y_1)\in W$ and $h_i(y_0)=h_i(y_1)=z_i$ for every $i\in[\ell]$.
--
--   The reduction $A'$ is fixed before $w$, $A$, $L$ and $W$, so it uses neither $L$, $W$ nor $\varepsilon_A$. This is the binding analysis of interactive hashing on which Theorem 4.1 rests; its proof is in Haitner–Reingold.
--
--   **Formalization Note** $A$ is accessed only through its next-message oracle with its coins fixed (rewinding); the probability is over $y$, the coins of $A$ and the random tape of $A'$ of length $p(w)2^v$. Running time counts the code length of $A'$ as well as its steps, as §3 prescribes for reductions.
--
--   Differences from the source:
--   - generalization: every algorithm A playing the role of S → every randomized strategy: an arbitrary function of its coins (from any finite nonempty set) and the received descriptions; reason: every algorithm is such a strategy, so the Lean statement specializes to the source
--   - reading: A′^A, each oracle call one step → an oracle machine with a query state; a query names a prefix h_1, …, h_i (or the final output) and is answered by the strategy with its coins fixed; reason: black-box rewinding access as described on p. 11
--   - reading: A′^A runs in time at most p(w)·2^v → steps plus code length of A′ at most p(w)·2^v, for every y ∈ {0,1}^w, every coin choice of A and every random tape of A′; reason: §3: the running time of a reduction includes its description
--   - reading: efficient family; ℓ polynomially bounded and polynomial-time computable → keys sampled exactly uniformly from κ(w) ≤ p(w) bits and functions evaluated by machines within p(w) steps; ℓ(w) ≤ p(w) computed from 1^w within p(w) steps; reason: §3.1: the families support uniform sampling and evaluation in polynomial time
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), Lemma 4.3, p. 10 (PDF p. 12)

import Mathlib
import Definitions.Def_SuccinctArgOWF_Kilian_InteractiveHashing

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

/-- Lemma 4.3 (binding of interactive hashing, [HR14, Theorem 3.7]), Dujmovic–Wichs p.10.
Construction 4.2 with `ℓ(w)` rounds and an efficient pairwise-independent family `H` from `{0,1}^w`
to `{0,1}^{v(w)}`: there are a polynomial `p`, a constant `c > 0` and one oracle machine `A'`, fixed
before `w`, the sender `A`, the set `L` and the relation `W`, such that `A'^A` (rewinding `A` on its
fixed coins through its next-message oracle, each call one step) runs within `p(w)·2^v` (steps plus
code length) and `Pr_{y ← L}[A'^A(y) ∈ W_y] ≥ c·ε_A² / (2^{10v} w^8) · min{1, 2^{vℓ}/|L|}`. -/
theorem hr_binding (H : HashFam) (ℓ : ℕ → ℕ) (hH : H.Efficient) (hPI : ∀ w, H.PairwiseIndep w)
    (hv : ∀ w, 1 ≤ H.v w) (hℓ : ∀ w, 1 ≤ ℓ w) (hℓc : PolyComputableBound ℓ) :
    ∃ (p : Polynomial ℕ) (c : ℝ) (A' : OracleMachine), 0 < c ∧
      ∀ (w : ℕ) (Ω : Type) [Fintype Ω] [Nonempty Ω] (A : HashSender Ω) (L : Finset Str)
        (W : Str → Str → Prop),
        L.Nonempty → (∀ y ∈ L, y.length = w) → (∀ x y, W x y → y ∈ L) →
        (∀ (ω : Ω) (y coins : Str), y.length = w → coins.length = p.eval w * 2 ^ H.v w →
          ∃ s, s + A'.encode.length ≤ p.eval w * 2 ^ H.v w ∧
            A'.HaltsAt (senderOracle A ω) [y, coins] s) ∧
        c * hashSuccess H w (ℓ w) A L W ^ 2 / ((2 : ℝ) ^ (10 * H.v w) * (w : ℝ) ^ 8) *
            min 1 ((2 : ℝ) ^ (H.v w * ℓ w) / (L.card : ℝ)) ≤
          prob (fun q : ↥L × Ω × (Fin (p.eval w * 2 ^ H.v w) → Bool) =>
            W (A'.outAt (senderOracle A q.2.1) [q.1.1, List.ofFn q.2.2]
              (p.eval w * 2 ^ H.v w)) q.1.1) := by sorry

end SuccinctArgOWF.Kilian
