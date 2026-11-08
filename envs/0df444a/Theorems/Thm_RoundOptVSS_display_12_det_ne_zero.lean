-- Prove2me | Theorems.Thm_RoundOptVSS_display_12_det_ne_zero
-- name    : RoundOptVSS.display_12_det_ne_zero
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:00:55.365212+00:00
-- url     : https://prove2.me/theorems/afea8aa4-ff34-4021-8c95-d60b3a0dd4a8
-- title:
--   Display (12) — $\det(\lambda I_r+A)\ne0$ when $A\in\mathbb F^{r\times r}$ and $\deg_{\mathbb F}\lambda>r$
-- statement:
--   **Display (12)** (proof of Lemma 8.2). Let $\mathbb E\supseteq\mathbb F$ be fields, $\lambda\in\mathbb E$ algebraic over $\mathbb F$ of degree $L$, and $A\in\mathbb F^{r\times r}$ with $r<L$. The polynomial $\det(ZI_r+A)\in\mathbb F[Z]$ is monic of degree $r<L$, so it cannot vanish at $\lambda$:
--
--   $$\det(\lambda I_r+A)\ne0,$$
--
--   and therefore for every right-hand side $v\in\mathbb E^r$ the system $(\lambda I_r+A)u=v$ has exactly one solution $u\in\mathbb E^r$ (in the paper, $v=-b_\Delta$).
--
--   This is why the compiler needs $\lambda$ of algebraic degree greater than $nm$: the privacy coupling of Lemma 8.2 and the hidden-point argument of Lemma B.1 both solve such a system.
--
--   Differences from the source:
--   - generalization: the right-hand side −b_∆ → every right-hand side v ∈ 𝔼^r; reason: the printed case is v = −b_∆
--   - encoding: λ of algebraic degree L over 𝔽 → IsIntegral 𝔽 lam with (minpoly 𝔽 lam).natDegree = L; reason: the degree of λ is the degree of its minimal polynomial
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), display (12) and the following sentences, proof of Lemma 8.2 (p.41)

import Mathlib

namespace RoundOptVSS

/-- **Display (12)**, proof of Lemma 8.2, p.41 of Liu-Zhang, Masserova, *Round-Optimal
Statistical Verifiable Secret Sharing with Polynomial Complexity*, manuscript (STOC 2027
submission, sha256 3a45d95d…): for `A ∈ 𝔽^{r×r}` and `λ ∈ 𝔼` of algebraic degree `L > r` over
`𝔽`, the polynomial `det(Z I_r + A) ∈ 𝔽[Z]` is monic of degree `r < L`, so it does not vanish at
`λ`; thus `(λ I_r + A) u = v` has a unique solution `u ∈ 𝔼^r` for every right-hand side (in
particular `v = −b∆`).

**Formalization Note.** `λ` is `lam`; "algebraic degree `L`" is `IsIntegral 𝔽 lam` with
`(minpoly 𝔽 lam).natDegree = L`; `A` acts on `𝔼^r` through `algebraMap 𝔽 𝔼`. -/
theorem display_12_det_ne_zero {𝔽 𝔼 : Type} [Field 𝔽] [Field 𝔼] [Algebra 𝔽 𝔼]
    (lam : 𝔼) (L : ℕ) (hlam : IsIntegral 𝔽 lam) (hL : (minpoly 𝔽 lam).natDegree = L)
    {r : ℕ} (A : Matrix (Fin r) (Fin r) 𝔽) (hr : r < L) :
    (lam • (1 : Matrix (Fin r) (Fin r) 𝔼) + A.map (algebraMap 𝔽 𝔼)).det ≠ 0 ∧
    ∀ v : Fin r → 𝔼, ∃! u : Fin r → 𝔼,
      (lam • (1 : Matrix (Fin r) (Fin r) 𝔼) + A.map (algebraMap 𝔽 𝔼)).mulVec u = v := by sorry

end RoundOptVSS
