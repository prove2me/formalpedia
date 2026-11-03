-- Prove2me | Theorems.Thm_WildeQIT_Wiretap_privInfo_additive
-- name    : WildeQIT.Wiretap.privInfo_additive
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:28:40.494931+00:00
-- url     : https://prove2.me/theorems/31154034-8e65-4c54-9ff4-fd7b5c07b27b
-- title:
--   Additivity of private information: $P(N_1\otimes N_2)=P(N_1)+P(N_2)$
-- statement:
--   **Theorem 13.2.1 (Additivity of Private Information).** Let $N_i$ be a classical wiretap channel with distribution $p_{Y_i,Z_i|X_i}$, for $i\in\{1,2\}$, with finite alphabets and nonempty input alphabets. The private information of the classical joint channel $N_1\otimes N_2$ is the sum of the individual private informations of the channels:
--
--   $$
--   P(N_1\otimes N_2)=P(N_1)+P(N_2).
--   $$
--
--   For the joint channel, Bob receives $Y_1Y_2$, Eve receives $Z_1Z_2$, and the maximization ranges over every auxiliary variable $U$ and every joint distribution $p_{U,X_1,X_2}$, so the inputs may be correlated.
--
--   Classical correlations between the inputs of independent wiretap channels therefore cannot increase their private information, and the regularized private information equals the single-letter one.
--
--   **Formalization Note** Alphabets are finite types (the book's setting) and information is measured in bits ($\log_2$). Distributions are the published `WildeQIT.FinDist`, channels the published `WildeQIT.Channel`, and $I(\cdot\,;\cdot)$ is the published `WildeQIT.mutualInfo` of a joint distribution (first component against second).
--
--   Differences from the source:
--   - encoding: P(N) ≡ max_{p_{U,X}} [I(U;Y) − I(U;Z)] over auxiliary U of any alphabet (13.57) → privInfo N, the supremum over U with alphabet Fin n for every n ∈ ℕ; reason: every finite alphabet is in bijection with some Fin n and mutual information is invariant under relabeling; the book does not prove attainment, so its max is read as the supremum of the same set
--   - encoding: the channels N1, N2 (implicitly nonempty: a channel has inputs) → [Nonempty] instance on each input alphabet; reason: with an empty input alphabet there is no input distribution and the book's quantity is undefined (Lean's junk value 0)
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.2.1, eq. (13.59), p. 397 (joint channel (13.60))

import Definitions.Def_WildeQIT_Wiretap_privInfo
import Definitions.Def_WildeQIT_Wiretap_prodWiretap

namespace WildeQIT.Wiretap

open WildeQIT

/-- **Theorem 13.2.1 (Additivity of Private Information).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.2.1, (13.59),
p. 397: let `Nᵢ` be a classical wiretap channel with distribution `p_{Yᵢ,Zᵢ|Xᵢ}`, for `i ∈ {1, 2}`.
The private information of the classical joint channel `N₁ ⊗ N₂` is the sum of the individual
private informations of the channels: `P(N₁ ⊗ N₂) = P(N₁) + P(N₂)`.

**Formalization Note.** `P` is `privInfo` (supremum over all finite auxiliary alphabets and all
joint distributions of `U` and the input); for the joint channel the input distribution is any
distribution of `(U, X₁, X₂)`, so the inputs may be correlated. Bob holds `Y₁Y₂`, Eve `Z₁Z₂`. The
input alphabets are nonempty. -/
theorem privInfo_additive {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type} [Fintype α₁] [Fintype α₂] [Fintype β₁]
    [Fintype β₂] [Fintype γ₁] [Fintype γ₂] [Nonempty α₁] [Nonempty α₂]
    (N₁ : WiretapChannel α₁ β₁ γ₁) (N₂ : WiretapChannel α₂ β₂ γ₂) :
    privInfo (prodWiretap N₁ N₂) = privInfo N₁ + privInfo N₂ := by sorry

end WildeQIT.Wiretap
