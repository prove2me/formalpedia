-- Prove2me | Theorems.Thm_Transcendence_norm_resultant_le_max_norm_eval
-- name    : Transcendence.norm_resultant_le_max_norm_eval
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-27T07:58:32.814704+00:00
-- url     : https://prove2.me/theorems/2a14f6ae-4226-47c6-a9ba-10c45a47e70b
-- title:
--   A Liouville inequality through the resultant: |Res(F, G)| is controlled by max(|F(θ)|, |G(θ)|)
-- statement:
--   Let $F, G \in \mathbb{C}[X]$ have Mahler measures $M(F), M(G) \ge 1$. Then for every $\theta \in \mathbb{C}$,
--
--   $$|\operatorname{Res}(F, G)| \le 2^{\deg F \deg G}\, M(F)^{\deg G}\, M(G)^{\deg F}\, \max\big(|F(\theta)|, |G(\theta)|\big).$$
--
--   Resultant and Mahler measure are Mathlib's `Polynomial.resultant` and `Polynomial.mahlerMeasure`. When $F, G \in \mathbb{Z}[X]$ are non-zero and coprime, the resultant is a non-zero integer and both Mahler measures are at least $1$, so the right-hand side is at least $1$: this is Corollary 3.7 of Roy–Waldschmidt (1997).
-- source:
--   D. Roy and M. Waldschmidt, Approximation diophantienne et indépendance algébrique de logarithmes, Ann. Sci. École Norm. Sup. (4) 30 (1997), 753–796, Corollary 3.7, in the complex form of their Lemma 3.4; they describe the inequality as well known and cite W. D. Brownawell (J. Number Theory 6, 1974), A. O. Gel'fond (Transcendental and Algebraic Numbers, 1952) and R. Tijdeman (Indag. Math. 33, 1971). Formal proof: Diaz modulus mission, 27 September 2026 (C. Perassi).

import Mathlib

namespace Transcendence

/-- A Liouville inequality through the resultant.

Let `F, G ∈ ℂ[X]` have Mahler measures at least `1`. Then at every point `θ`,
`|Res(F, G)| ≤ 2^(deg F · deg G) · M(F)^(deg G) · M(G)^(deg F) · max(|F(θ)|, |G(θ)|)`.

Let `α₁` be the root of `F` or `G` nearest to `θ`, say a root of `F`. Writing the resultant as
`a^(deg G) ∏ G(α)` over the roots `α` of `F`, the factor `G(α₁)` is at most `2^(deg G) |G(θ)|`,
because every root `β` of `G` has `|α₁ - β| ≤ 2 |θ - β|`, and each other factor `G(α)` is at most
`2^(deg G) max(1, |α|)^(deg G) M(G)`. If neither polynomial has a root, both are constants and the
resultant is `1 ≤ M(F) = |F(θ)|`. This is the complex form of the inequality of Roy–Waldschmidt
(1997), Corollary 3.7, proved as in their Lemma 3.4: when `F, G ∈ ℤ[X]` are coprime, the resultant
is a non-zero integer and the right-hand side is at least `1`. -/
theorem norm_resultant_le_max_norm_eval (F G : Polynomial ℂ) (hF : 1 ≤ F.mahlerMeasure)
    (hG : 1 ≤ G.mahlerMeasure) (θ : ℂ) :
    ‖F.resultant G‖ ≤ 2 ^ (F.natDegree * G.natDegree) * F.mahlerMeasure ^ G.natDegree *
      G.mahlerMeasure ^ F.natDegree * max ‖F.eval θ‖ ‖G.eval θ‖ := by
  sorry

end Transcendence
