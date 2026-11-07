-- Prove2me | Theorems.Thm_SetMultCost_corollary_2_7
-- name    : SetMultCost.corollary_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:29.616204+00:00
-- url     : https://prove2.me/theorems/ae9d7175-e418-4f89-92d9-bcd13e193756
-- title:
--   Corollary 2.7 (corrected: there is a partition) — relative rank of the hard polynomial
-- statement:
--   Let $\alpha\in(0,1]$, $n\ge4$, $d\ge1$. There are a partition $\pi=(\mathcal P,\mathcal N)$ of $[d]$ and a part-preserving projection $P_\alpha$ of $\mathrm{IMM}_{n,d}$, set-multilinear for the partition, such that
--
--   $$\mathrm{relrk}_{n,\alpha,\pi}(P_\alpha)\ge2^{-3d/2}\cdot\frac{1}{n^{|\alpha d_{\mathcal P}-d_{\mathcal N}|/2}},$$
--
--   and $|\alpha d_{\mathcal P}-d_{\mathcal N}|\le2$ whenever $2d\le\log_2n$. Moreover every circuit $\Phi$ for $\mathrm{IMM}_{n,d}$ yields a circuit for $P_\alpha$ of the same size, with every bound on the product-depth preserved, and set-multilinear if $\Phi$ is.
--
--   Differences from the source:
--   - correction: π arbitrary, with P_α as the proof constructs it, a width-n ABP → there exists π, with P_α a part-preserving projection of IMM_{n,d}; reason: the projection form is false for arbitrary π: n = 128, α = 1, d = 4, P = {1,2} has rank ≤ 128 at the middle cut, so relrk ≤ 1/128 < 2^{−6}; the proof of Theorem 1.2 only needs one π
--   - generalization: "If there is a set-multilinear circuit computing IMM_{n,d}" → every circuit for IMM_{n,d}, keeping set-multilinearity when present; reason: the substitution applies to any circuit, and the proof of Theorem 1.2 projects before set-multilinearizing; specializes to the printed form
--   - generalization: no bound on |αd_P − d_N| in the statement → the clause 2d ≤ log₂ n → |αd_P − d_N| ≤ 2; reason: the proof of Theorem 1.2 chooses such a partition; an added conjunct
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Corollary 2.7, p.10; proof of Theorem 1.2, p.24

import Mathlib
import Definitions.Def_SetMultCost_Circuit
import Definitions.Def_SetMultCost_Circuit_HasProductDepthLE
import Definitions.Def_SetMultCost_IsSetMultilinearOn
import Definitions.Def_SetMultCost_Circuit_IsSetMultilinear
import Definitions.Def_SetMultCost_imm
import Definitions.Def_SetMultCost_relrk
import Definitions.Def_SetMultCost_projection

namespace SetMultCost

/-- **Corollary 2.7 (corrected).** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.10: "Let α ∈ (0, 1] and n ≥ 4. If there is a
set-multilinear circuit computing IMMn,d of size s and product-depth ∆, then there is also a
set-multilinear circuit of size s and product-depth ∆ computing a polynomial Pα such that
relrkn,α,π(Pα) ≥ 2^{−3d/2} · 1/n^{|αdP−dN|/2}."

**Formalization Note.** A correction: "π" becomes "there is a π", and `Pα` is tied to `IMM_{n,d}` as a
projection, which is what the proof constructs and Theorem 1.2 needs. For arbitrary `π` that form is
false: at `n = 128`, `α = 1`, `d = 4`, `P = {1,2}`, a width-`128` projection has rank at most `128` at the
middle cut, so relative rank at most `1/128`, below the printed `2^{−6}`. The clause `2d ≤ log₂ n → |α d_P − d_N| ≤ 2` is what the proof
of Theorem 1.2 (p.24) means by "Choose a partition". A generalization: the transfer covers every
circuit `Φ` for `IMM_{n,d}`, keeping the size and every bound on the product-depth, and it keeps
set-multilinearity when `Φ` has it. The proof of Theorem 1.2 needs this form, since it projects
before set-multilinearizing. -/
theorem corollary_2_7 (F : Type*) [Field F] (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n d : ℕ)
    (hn : 4 ≤ n) (hd : 1 ≤ d) :
    ∃ (P : Finset (Fin d)) (ρ : IMMVar n d → Option (Var d (sizeFn P ⌊(n : ℝ) ^ α⌋₊ n))),
      IsPartPreserving Prod.fst Sigma.fst ρ ∧
      IsSetMultilinearOn Sigma.fst Finset.univ (projection F ρ (imm F n d)) ∧
      (2 : ℝ) ^ (-(3 * (d : ℝ) / 2)) * (1 / (n : ℝ) ^ (|α * (P.card : ℝ) - (Pᶜ.card : ℝ)| / 2)) ≤
        relrk n α P Finset.univ (projection F ρ (imm F n d)) ∧
      (2 * (d : ℝ) ≤ Real.logb 2 n → |α * (P.card : ℝ) - (Pᶜ.card : ℝ)| ≤ 2) ∧
      ∀ Φ : Circuit (IMMVar n d) F, Φ.value = imm F n d →
        ∃ Φ' : Circuit (Var d (sizeFn P ⌊(n : ℝ) ^ α⌋₊ n)) F,
          Φ'.value = projection F ρ (imm F n d) ∧ Φ'.size = Φ.size ∧
          (∀ Δ, Φ.HasProductDepthLE Δ → Φ'.HasProductDepthLE Δ) ∧
          (Φ.IsSetMultilinear Prod.fst → Φ'.IsSetMultilinear Sigma.fst) := by sorry

end SetMultCost
