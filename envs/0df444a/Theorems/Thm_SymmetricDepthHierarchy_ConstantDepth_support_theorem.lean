-- Prove2me | Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_support_theorem
-- name    : SymmetricDepthHierarchy.ConstantDepth.support_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:33.733935+00:00
-- url     : https://prove2.me/theorems/caa62957-2aed-4261-88ca-6376dbdbe351
-- title:
--   Theorem 2.6 (Support theorem): orbit size $\le f(n)$ forces minimal supports of size $\le\kappa_f(n)-1$
-- statement:
--   Let $f:\mathbb N\to\mathbb N$ and let $n\ge20$ be such that $3\kappa_f(n)\le n+2$, where $\kappa_f(n)=\min\{r\in\mathbb N:\binom nr>f(n)\}$. Let $C$ be a reduced matrix-symmetric circuit over $X_n$ of orbit size $\le f(n)$. Then every gate $g$ of $C$ has a minimal support, of size
--   $$|\sup(g)|\le\kappa_f(n)-1.$$
--
--   Small orbits therefore force small supports; polynomial orbit size corresponds to constant support size.
--
--   Differences from the source:
--   - encoding: [n] = {1,…,n}, variables x_{i,j} → Fin n (0-based), variables indexed by Fin n × Fin n; reason: relabelling of [n]; the same polynomials and circuits
--   - encoding: κ_f(n) ∈ ℕ (a minimum); size ≤ κ_f(n) − 1 → kappa f n ∈ ℕ∞ (⊤ for an empty set); |sup(g)| + 1 ≤ kappa f n; reason: 3κ ≤ n + 2 forces κ finite; the +1 form avoids truncated subtraction
--   - encoding: g has a minimal support → sup(g) (the intersection of the small supports) is itself a small support of g; reason: by [DPS26a, Lemmas 2.1, 2.2] this is exactly the existence of the unique minimal small support
--   - encoding: S supports g if the pointwise stabiliser Stab•(S) ≤ Γ_n fixes g (C rigid) → every automorphism extending an element of the pointwise stabiliser of S fixes g; reason: for a rigid circuit each element has exactly one extension, so the two agree; supports are only applied to reduced (hence rigid, Lemma 2.3) circuits or to rigidifications
--   - reading: sup(g): the unique minimal support, 'contained in every support of g' → sup(g) := intersection of all supports with fewer than n/2 points on each side; reason: containment in every support is false for large supports (n = 20, the reduced circuit summing all 400 variables: {L1,R1} and {L2,…,L20,R1} both support x_{1,1}); by [DPS26a, Lemmas 2.1, 2.2] the intersection of the small supports is the unique minimal small support, the only object the source's later arguments use
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 8 (PDF p. 11), Theorem 2.6; proof in Appendix A, pp. 27–28 (PDF pp. 30–31)

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Circuit
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Support

open scoped Classical

namespace SymmetricDepthHierarchy.ConstantDepth

/-- Theorem 2.6 (Support theorem), printed p. 8 (PDF p. 11). Let `f : ℕ → ℕ` and let `n ≥ 20` be
such that `3 κ_f(n) ≤ n + 2`. Then every gate of a reduced matrix-symmetric circuit of orbit size
`≤ f(n)` has a minimal support of size `≤ κ_f(n) − 1`: the minimal support `sup(g)` is itself a
small support (fewer than `n/2` points on each side), and `|sup(g)| + 1 ≤ κ_f(n)`. -/
theorem support_theorem {K : Type} [Field K] [CharZero K] (f : ℕ → ℕ) (n : ℕ) (hn : 20 ≤ n)
    (hκ : 3 * kappa f n ≤ ((n + 2 : ℕ) : ℕ∞))
    {V : Type} [Fintype V] (C : Circuit K n V) (hC : C.WellFormed) (hsym : C.MatrixSymmetric)
    (hred : C.Reduced) (horb : C.maxOrb ≤ f n) :
    ∀ g : V, C.IsSmallSupport g (C.minSup g) ∧ ((C.minSup g).card : ℕ∞) + 1 ≤ kappa f n := by sorry

end SymmetricDepthHierarchy.ConstantDepth
