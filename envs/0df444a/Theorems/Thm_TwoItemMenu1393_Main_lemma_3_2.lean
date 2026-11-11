-- Prove2me | Theorems.Thm_TwoItemMenu1393_Main_lemma_3_2
-- name    : TwoItemMenu1393.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:24:37.094344+00:00
-- url     : https://prove2.me/theorems/485aede5-c72f-4506-8aa1-0309b5e2dc73
-- title:
--   Lemma 3.2 — Price-discount payment and revenue bounds
-- statement:
--   Let $0<\delta\le1/2$, $\lambda=(1-\delta)^{-1}$, and $\eta\ge0$. Let $u,\tilde u\in\mathcal U$, with $\tilde u\le u$ on all of $\mathbb R^2$ and $\tilde u\ge u-\eta$ on $[0,\lambda]^2$. If $\tilde u$ is induced by a menu $S$, discount every price by $1-\delta$ and let $w$ be the resulting utility. Then $w\in\mathcal U$. Every Borel maximizing actual-entry selection for this menu has size at most its number of nonnull entries. For every Borel subgradient selection of $w$, every selection of $u$, and every type $v\in[0,1]^2$,
--   $$p_w(v)\ge(1-\delta)p_u(v)-\frac{(1-\delta)^2\eta}{\delta}\ge p_u(v)-2\delta-\frac{\eta}{\delta}.$$
--   Consequently, $\mathrm{Rev}_F(w)\ge\mathrm{Rev}_F(u)-2\delta-\eta/\delta$ for every Borel law $F$ on the square. Mixtures at ties are allowed in the payment and revenue assertions. These bounds turn utility approximation into revenue approximation without a density assumption.
--
--   Differences from the source:
--   - encoding: two real coordinates → EuclideanSpace ℝ (Fin 2); reason: the coordinate isometry preserves dot products, Borel sets, Euclidean norms and all instances
--   - encoding: Borel probability laws on the type square → ambient Borel measures with total mass one and zero mass off the square; reason: pushforward along the square inclusion gives precisely the same laws and integrals
--   - encoding: menu cardinality, including possibly infinite menus → a size bound for every finite bound N on the nonnull menu; no finite cardinality assumption for utility and payment bounds; reason: an infinite menu has no finite cardinality bound, while the finite conditional covers every finite menu exactly
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), Lemma 3.2, p. 7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf#page=7

import Definitions.Def_TwoItemMenu1393_Main_Model
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace TwoItemMenu1393.Main

/-- Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393
(October 2026), Lemma 3.2, p. 7.
Pinned PDF sha256: 9b1049b1045e4c9f8fe08a35eb33749c850548cb87464793e3f41f1b615fbb3e. -/
theorem lemma_3_2 (M : Mechanism) (hM : Admissible M)
    (δ η : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1/2) (hη : 0 ≤ η)
    (u' : Vec → ℝ) (hu' : Utility u') (S : Set Entry) (hS : ValidMenu S)
    (henv : u' = envelope S) (hle : ∀ v : Vec, u' v ≤ M.u v)
    (happrox : ∀ v ∈ square ((1-δ)⁻¹), M.u v - η ≤ u' v) :
    let w := envelope (discount δ S)
    Utility w ∧
      (∀ (N : ℕ) (W : Mechanism),
        (∃ E : Finset Entry, (↑E : Set Entry) = S \ {nullEntry} ∧ E.card ≤ N) →
        GlobalEntrySelection W (discount δ S) → MenuSizeAtMost W N) ∧
      ∀ W : Mechanism, W.u = w → Selection w W.g →
        (∀ v ∈ square 1,
          (1-δ)*payment M v - (1-δ)^2*η/δ ≤ payment W v ∧
          payment M v - 2*δ - η/δ ≤ (1-δ)*payment M v - (1-δ)^2*η/δ) ∧
        ∀ F : Measure Vec, Law F → revenue F M - 2*δ - η/δ ≤ revenue F W := by sorry

end TwoItemMenu1393.Main
