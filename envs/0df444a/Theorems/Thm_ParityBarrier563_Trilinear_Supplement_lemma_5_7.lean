-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_lemma_5_7
-- name    : ParityBarrier563.Trilinear.Supplement.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:49:53.427913+00:00
-- url     : https://prove2.me/theorems/c1a36438-a760-4912-be37-b0207f1ff162
-- title:
--   Lemma 5.7 — Hash injectivity and polynomial-evaluation tail bound
-- statement:
--   Let $n\ge64$, $r=\lceil n^{2/3}\rceil$, t the largest even integer with $t^6\le n$, and fix any irreducible monic degree-r polynomial P over $\mathbb F_2$. Let σ restrict the n data coordinates, $T=\operatorname{live}(\sigma)$ and $J:\{0,1\}^T\to[-1,1]$. A uniformly random Hankel hash U fails to be injective on the points extending σ with probability at most $2^{|T|-r}$. For every injective such U, choose independent uniform $\beta_0,\ldots,\beta_{t-1}\in\mathbb F_2[Z]/(P)$. For g the sign of the acceptance predicate $[Z^0]\sum_{j<t}\beta_j h(x)^j=0$,
--   $$\Pr_\beta\left[|\mathbb E[g_\sigma J]|>2^{-|T|/4}\right]\le t^{t/2}2^{-t|T|/4}.$$
--   Both the hash failure estimate and the tail estimate for every injective hash are included. These give the hard slices for hashed evaluation.
--
--   Differences from the source:
--   - encoding: field quotient and uniform ring elements → monic coefficient bits, polynomial remainders, and uniform coefficient cubes; reason: irreducibility is assumed only in this support lemma; coefficient encoding is a bijection
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Lemma 5.7, printed p.20 / PDF p.22

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_HashedEvaluation

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Lemma 5.7: both the hash failure bound and the tail bound for every injective hash. -/
theorem lemma_5_7 (n : ℕ) (hn : 64 ≤ n) (Pbits : Fin (hashR n) → Bool)
    (hP : Irreducible (hashModulus Pbits)) (σ : Restriction (Fin n))
    (J : RealFn (Live σ)) (hJ : BoundedTest J) :
  probability (fun U : Fin (n+hashR n-1) → Bool =>
    ¬ Function.Injective (fun z : Live σ → Bool => hankelHash U (fill σ z))) ≤
      (2 : ℝ)^((Fintype.card (Live σ) : ℝ)-hashR n) ∧
  ∀ U : Fin (n+hashR n-1) → Bool,
    Function.Injective (fun z : Live σ → Bool => hankelHash U (fill σ z)) →
    probability (fun β : Fin (hashT n) × Fin (hashR n) → Bool =>
      |avg (fun z => restrict σ (sgn (hashAccept U (hashModulus Pbits) β)) z * J z)| >
        (2 : ℝ)^(-(Fintype.card (Live σ) : ℝ)/4)) ≤
      (hashT n : ℝ)^(hashT n/2) *
        (2 : ℝ)^(-((hashT n : ℝ)*Fintype.card (Live σ))/4) := by sorry

end ParityBarrier563.Trilinear.Supplement
