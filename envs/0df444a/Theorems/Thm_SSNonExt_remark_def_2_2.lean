-- Prove2me | Theorems.Thm_SSNonExt_remark_def_2_2
-- name    : SSNonExt.remark_def_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:55:48.914872+00:00
-- url     : https://prove2.me/theorems/c90eec6e-8377-46fa-b9ba-ebdebb5a870e
-- title:
--   Remark after Definition 2.2 — projecting to the first bit does not increase the error
-- statement:
--   Let $K$ be a finite set, $P$ a distribution on $K$, $\ell\ge1$ and $\mathrm{Ext}:K\to\{0,1\}^\ell$. Writing $\mathrm{Ext}(k)_1$ for the first bit,
--
--   $$\mathrm{TV}\big(\mathrm{Ext}(K)_1,U_1\big)\le\mathrm{TV}\big(\mathrm{Ext}(K),U_\ell\big),\qquad K\sim P.$$
--
--   Taking the supremum over a class $\mathcal S$ gives $\mathrm{err}(\mathrm{Ext}_1,\mathcal S)\le\mathrm{err}(\mathrm{Ext},\mathcal S)$ (Definition 2.2), so a lower bound on one-bit error applies to every output length.
--
--   Differences from the source:
--   - generalization: the error err(Ext, 𝒮) = sup_{P∈𝒮} TV(Ext(K), U) does not increase → the inequality for each distribution P; reason: taking the supremum over 𝒮 gives the stated form
--   - encoding: projection to the first bit, U₁ → coordinate 0 of Fin ℓ → Bool, uniform law on Bool; reason: the same map and law
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), §2, remark after Definition 2.2, p.6 (PDF p.6)

import Mathlib
import Definitions.Def_SSNonExt_TV

namespace SSNonExt

/-- **Remark after Definition 2.2.** "Composing an ℓ-bit extractor with the projection to its first bit
does not increase the error, so a lower bound on one-bit error applies to every output length."
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), §2, remark after Definition 2.2, p.6 (PDF p.6).

For every distribution `P` on a finite key set, every `ℓ ≥ 1` and every `Ext : K → {0,1}^ℓ`,
`TV(Ext(K)₁, U₁) ≤ TV(Ext(K), U_ℓ)` with `K ∼ P`, where `Ext(K)₁` is the first bit.

**Formalization Note.** Stated for each distribution `P`; taking the supremum over a class gives the
statement for `err(Ext, 𝒮)` of Definition 2.2. The first bit is coordinate `0` of `Fin ℓ → Bool`. -/
theorem remark_def_2_2 {K : Type*} [Fintype K] (P : PMF K) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (Ext : K → Fin ℓ → Bool) :
    TV (P.map fun k => Ext k ⟨0, hℓ⟩) (PMF.uniformOfFintype Bool) ≤
      TV (P.map Ext) (PMF.uniformOfFintype (Fin ℓ → Bool)) := by sorry

end SSNonExt
