-- Prove2me | Theorems.Thm_WHAdditivity_Renyi_meo_additive
-- name    : WHAdditivity.Renyi.meo_additive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:01.782995+00:00
-- url     : https://prove2.me/theorems/7d37b2e2-e60a-4299-a34e-fefa842bd7f4
-- title:
--   (7), p. 3 — for 1 ≤ p ≤ 2 the minimal p-Rényi output entropy of ⊗ⱼ Γ_{dⱼ} is the sum of the single-channel values
-- statement:
--   Let $N\in\mathbb N$ and $d_1,\dots,d_N\ge2$. For each $j$ let $\Gamma_{d_j}$ be the Werner–Holevo channel $\Gamma_{d}(X) = \frac{1}{d-1}\bigl(\operatorname{Tr}(X)\,\mathbb 1 - X^{\mathsf T}\bigr)$ on $d_j\times d_j$ matrices, and let $\bigotimes_{j=1}^N\Gamma_{d_j}$ be their tensor product, a linear map on matrices of $\bigotimes_{j=1}^N\mathbb C^{d_j}$. For $p\ge1$ let $S_p(\rho) = -\frac{1}{p-1}\log\operatorname{Tr}\rho^p$ ($p>1$) and $S_1 = S$ the von Neumann entropy, with the natural logarithm, and let
--   $$\mathrm{MEO}_p[\Phi] = \inf_{\varphi,\ \|\varphi\|=1}S_p\bigl(\Phi(|\varphi\rangle\langle\varphi|)\bigr)$$
--   be the minimal $p$-Rényi output entropy (1), the infimum over all unit input vectors — for the product channel, over all unit vectors of $\bigotimes_j\mathbb C^{d_j}$, entangled ones included.
--
--   Then for every $1\le p\le2$ the sets of output entropies of $\bigotimes_j\Gamma_{d_j}$ and of each $\Gamma_{d_j}$ are bounded below, and
--
--   $$\mathrm{MEO}_p\Bigl[\bigotimes_{j=1}^N\Gamma_{d_j}\Bigr] = \sum_{j=1}^N\mathrm{MEO}_p\bigl[\Gamma_{d_j}\bigr].$$
--
--   This is the multiple additivity of the minimal output entropy of the Werner–Holevo channels, for arbitrary numbers of factors and arbitrary, possibly different, dimensions: entangled inputs cannot lower the output entropy below what product inputs achieve.
--
--   **Formalization Note.** $\bigotimes_j\Gamma_{d_j}$ is the generic matrix-unit tensor product of the definitions file applied to the family $\Gamma_{d_j}$; it is not defined through its value on pure states. $\mathrm{MEO}_p$ is a real `sInf`, which is why bounded-belowness is part of the conclusion.
--
--   Differences from the source:
--   - encoding: Γ_{d_j} with 1/(d_j − 1) → hypotheses 2 ≤ d_j; reason: (6) is undefined at d_j = 1; Lean's 0⁻¹ = 0 would make it the zero map.
--   - encoding: Γ_d(ρ) = (1/(d−1))(𝟙 − ρᵀ) on density matrices, and ⊗_j Γ_{d_j} → the linear extension (Tr X · 𝟙 − Xᵀ)/(d − 1), tensored through matrix units; reason: the product channel acts on entangled inputs, which needs Γ_d as a linear map; it agrees with (6) on density matrices.
--   - encoding: MEO_p at p = 1 defined as the limit p ↓ 1 → S_1 := S, the von Neumann entropy; reason: the paper extends the notation to p = 1 by this limit, whose value is the von Neumann MEO.
--   - encoding: MEO_p as an infimum → real `sInf`, with bounded-belowness of each set concluded; reason: Lean's `sInf` of a set unbounded below is 0; concluding the bound excludes the junk case.
--   - encoding: log unspecified → natural logarithm; reason: both sides scale by the same factor under a change of base.
--   - encoding: sites 1, …, N → sites `Fin N` from 0; reason: relabelling only.
--   - generalization: N ≥ 1 implicitly → every N ∈ ℕ; reason: at N = 0 both sides are 0 (one-dimensional output, empty sum); specializes to the paper's N ≥ 1.
-- source:
--   Alicki, Fannes, Note on multiple additivity of minimal Renyi entropy output of the Werner–Holevo channels, arXiv:quant-ph/0407033v2, p. 3, (7)

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

namespace WHAdditivity.Renyi

theorem meo_additive (N : ℕ) (d : Fin N → ℕ) (hd : ∀ j, 2 ≤ d j) (p : ℝ) (hp1 : 1 ≤ p)
    (hp2 : p ≤ 2) :
    BddBelow (outputEntropies p (tensorChannel d fun j => wernerHolevo (d j))) ∧
    (∀ j, BddBelow (outputEntropies p (wernerHolevo (d j)))) ∧
    minOutputEntropy p (tensorChannel d fun j => wernerHolevo (d j)) =
      ∑ j, minOutputEntropy p (wernerHolevo (d j)) := by sorry

end WHAdditivity.Renyi
