-- Prove2me | Theorems.Thm_SetMultCost_lemma_4_2
-- name    : SetMultCost.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:22.8432+00:00
-- url     : https://prove2.me/theorems/56fca23f-2de1-4f6c-a85e-ca26e5ef92fa
-- title:
--   Lemma 4.2 (homogeneous: every node) — $(\tau,S)$-product decomposition
-- statement:
--   Let $\mathbf r$ be a sequence of restrictions and let $\Phi$ be an $\mathbf r$-restricted homogeneous circuit of size $s$ and product-depth at most $\Delta$, computing a polynomial homogeneous of degree $d$. Let $\tau=(\tau_0,\dots,\tau_\Delta)$ be non-decreasing with $\tau_\Delta<d$ and $\tau_0=1$, and let $S\subseteq[\Delta]$ be the coordinates with $\tau_i<r_i\tau_{i-1}$. Then
--
--   $$\Phi=\sum_{i\le s}G_{i1}\cdots G_{ir_i},$$
--
--   with at most $s$ summands, each a $(\tau,S)$-product. Moreover each factor is homogeneous; and if $\Phi$ is a set-multilinear circuit whose value is set-multilinear on $T$, the factors of each summand are set-multilinear on disjoint sets of parts with union $T$.
--
--   This turns a circuit into a small sum of products, each with many low-degree factors, on which the relative rank is small.
--
--   Differences from the source:
--   - reading: "homogeneous circuit", whose p.8 sentence says every node has degree at most d → every node homogeneous; reason: the lemma's term and its proof (p.14: "degrees do not decrease at any sum gate in a homogeneous circuit") use the standard meaning, which the p.8 sentence does not give (x₁⋯x_d + x₁ has every node of degree ≤ d and a sum gate with a child of degree 1); the paper applies the lemma only to set-multilinear circuits, which are homogeneous in this sense
--   - reading: "any syntactic restriction on Φ (such as set-multilinearity)" → factors homogeneous; set-multilinear on disjoint parts with union T; reason: the only restrictions the paper uses
--   - generalization: Φ computing a polynomial of degree d → value homogeneous of degree d, allowing 0; reason: the zero value has the empty decomposition; a degree-d value of a homogeneous circuit is an instance
--   - encoding: s summands → at most s summands; reason: the proof removes at least one edge per summand; empty summands can pad the sum only with the zero product
--   - encoding: product-height in layered circuits → an existential height function; reason: layer heights are one such function
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Lemma 4.2, p.13; §2, p.8

import Mathlib
import Definitions.Def_SetMultCost_Circuit
import Definitions.Def_SetMultCost_Circuit_IsRestricted
import Definitions.Def_SetMultCost_Circuit_IsHomogeneous
import Definitions.Def_SetMultCost_IsSetMultilinearOn
import Definitions.Def_SetMultCost_Circuit_IsSetMultilinear
import Definitions.Def_SetMultCost_IsTauSProduct

namespace SetMultCost

/-- **Lemma 4.2.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.13: "Let r ∈ (N ∪ ∞)^∆ be a sequence of restrictions. Let Φ be a
r-restricted homogeneous circuit of size s and product-depth ∆, computing a polynomial of degree d.
Fix any τ = (τ0, τ1, . . . , τ∆) ∈ N^{∆+1}_{≥0} that is non-decreasing with τ∆ < d and τ0 = 1. Let
S = {i1, . . . , iℓ} ⊆ [∆] be the coordinates where τi < riτi−1. Then Φ can be expressed as: Φ =
∑_{i=1}^s Gi1 · · · Giri where each {Gi1, . . . , Giri} is a (τ,S)-product. Moreover, any syntactic
restriction on Φ (such as set-multilinearity) continues to hold for the terms Gi1 · · · Giri."

**Formalization Note.** "Homogeneous" means every node (`Circuit.IsHomogeneous`). "Computing a
polynomial of degree `d`" is homogeneity of degree `d` of the value, which is what remains when the
value is `0` (the empty decomposition). The decomposition has at most `s` summands. "Any syntactic
restriction" is read as the two the paper uses: each factor is homogeneous, and for a set-multilinear
`Φ` whose value is set-multilinear on `T`, the factors of each summand are set-multilinear on disjoint
sets of parts with union `T`. -/
theorem lemma_4_2 {σ F ι : Type*} [Field F] [DecidableEq ι] (r : ℕ → ℕ∞) (Δ d : ℕ) (τ : ℕ → ℕ)
    (Φ : Circuit σ F) (hr : Φ.IsRestricted Δ r) (hhom : Φ.IsHomogeneous)
    (hdeg : Φ.value.IsHomogeneous d) (hτ : MonotoneOn τ (Set.Iic Δ)) (hτd : τ Δ < d) (hτ0 : τ 0 = 1)
    (part : σ → ι) (T : Finset ι) :
    ∃ Gs : List (List (MvPolynomial σ F)),
      Gs.length ≤ Φ.size ∧ Φ.value = (Gs.map List.prod).sum ∧
      ∀ G ∈ Gs, IsTauSProduct τ (tauS Δ r τ) G ∧
        (∀ g ∈ G, ∃ k : ℕ, g.IsHomogeneous k) ∧
        (Φ.IsSetMultilinear part → IsSetMultilinearOn part T Φ.value →
          IsSetMultilinearProduct part T G) := by sorry

end SetMultCost
