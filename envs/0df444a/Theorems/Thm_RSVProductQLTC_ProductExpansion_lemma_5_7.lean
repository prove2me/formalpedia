-- Prove2me | Theorems.Thm_RSVProductQLTC_ProductExpansion_lemma_5_7
-- name    : RSVProductQLTC.ProductExpansion.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:32.609401+00:00
-- url     : https://prove2.me/theorems/e6d30aa6-9409-445c-ae96-6fff0b241867
-- title:
--   Lemma 5.7 — projective product expansion
-- statement:
--   Assume Conjecture 5.6. Fix $r\ge2$, $0<\eta<1$ and $\beta\ge1$. There is one $\rho>0$, depending only on $r,\eta,\beta$, with the following property. Let $E=\mathbb F_{2^e}$, let $m_1,\ldots,m_r$ be positive integers with $2m_i\mid e$, and put $s_i=2^{m_i}$. Require the $s_i+1$ to be pairwise coprime and $\max_i(s_i+1)\le\beta\min_i(s_i+1)$. For each $i$, let $K_i=\mathbb F_{s_i}$ be included in $E$, choose $0\le d_i\le s_i-1$, and set $C_i=\operatorname{PRS}_{d_i}(K_i;E)$. If
--   $$\eta\le\frac{d_i+1}{s_i+1}\le1-\eta\qquad\text{for every }i,$$
--   then every nonempty subtuple of $(C_i)$ and every nonempty subtuple of $(C_i^\perp)$ is $\rho$-product-expanding, with this same $\rho$.
--
--   The constant is uniform over $E,e,m_i,d_i$, the subtuple, and the primal or dual choice. Singleton subtuples are included, and each subtuple has its own product grid. This is the conditional source of expansion for the projective local codes.
--
--   Differences from the source:
--   - encoding: indices 1 through r and nonnegative degrees → Fin r and natural degrees; reason: only index names change; all r entries and all admissible degrees remain
--   - encoding: binary extension field with subfields of size 2^m_i → finite field types with characteristic and cardinality data and field homomorphisms; reason: every source field and inclusion has this presentation; no code existence or expansion is added to the hypotheses
--   - encoding: maximum size at most beta times minimum size → all pairwise real size inequalities; reason: equivalent for a nonempty finite tuple of positive sizes
--   - encoding: RS maximum degree d and all nonempty subtuples → published affine RS degree-less-than argument d+1 and Finset subtypes with their own product grids; reason: preserves the polynomial space and includes singleton subtuples
-- source:
--   Mitali Bafna, Anqi Li, Quynh T. Nguyen, STOC 2027 submission #1136 (October 2026), Lemma 5.7, printed p.20 (PDF p.21)

import Mathlib
import Definitions.Def_RSVProductQLTC_ProductExpansion_conjecture_5_6
import Definitions.Def_RSVProductQLTC_ProductExpansion_subtuplePE
import Definitions.Def_RSVProductQLTC_ProductExpansion_projectiveRS
set_option autoImplicit false
open Classical

namespace RSVProductQLTC.ProductExpansion

/-- Lemma 5.7, printed p.20 (PDF p.21). All nonempty primal and dual subtuples share one constant. -/
theorem lemma_5_7 (hc : conjecture_5_6) (r : ℕ) (hr : 2 ≤ r)
    (η β : ℝ) (hη : 0 < η) (hη1 : η < 1) (hβ : 1 ≤ β) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (E : Type) [Field E] [Fintype E] [CharP E 2] (e : ℕ),
        Fintype.card E = 2 ^ e →
        ∀ (m : Fin r → ℕ), (∀ i, 0 < m i ∧ 2 * m i ∣ e) →
          (∀ i j, i ≠ j → Nat.Coprime (2 ^ m i + 1) (2 ^ m j + 1)) →
          (∀ i j, ((2 ^ m i + 1 : ℕ) : ℝ) ≤ β * ((2 ^ m j + 1 : ℕ) : ℝ)) →
          ∀ (K : Fin r → Type) [∀ i, Field (K i)] [∀ i, Fintype (K i)]
            (ι : ∀ i, K i →+* E),
            (∀ i, Fintype.card (K i) = 2 ^ m i) →
            ∀ (d : Fin r → ℕ), (∀ i, d i ≤ 2 ^ m i - 1) →
              (∀ i, η ≤ ((d i + 1 : ℕ) : ℝ) / ((2 ^ m i + 1 : ℕ) : ℝ) ∧
                ((d i + 1 : ℕ) : ℝ) / ((2 ^ m i + 1 : ℕ) : ℝ) ≤ 1 - η) →
                allSubtuplePE ρ (fun i => projectiveRS (ι i) (d i)) ∧
                allSubtuplePE ρ (fun i => GoodQLTC.dualCode (projectiveRS (ι i) (d i))) := by sorry

end RSVProductQLTC.ProductExpansion
