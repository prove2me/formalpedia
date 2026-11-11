-- Prove2me | Theorems.Thm_PolySwap_KMS_theorem_3_1
-- name    : PolySwap.KMS.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:42:41.136464+00:00
-- url     : https://prove2.me/theorems/4123f6d1-5687-41c7-8151-72a643d11a82
-- title:
--   Theorem 3.1 — the $n$-skeleton of $X(A_d,\mathbb F_q,f)$ is a $(c\,r^{-34},r,\Lambda)$-swap coboundary expander and a $\gamma_1$-local spectral expander
-- statement:
--   There are absolute constants $c>0$ and $C\ge1$ such that the following holds. Let $r\in\mathbb N$, $r\ge10^4$, and fix $d\ge r^{55}$, a spectral parameter $\gamma_1$ with
--   $$\frac{r+1}{d-r^{11}-r^{10}-2}\le\gamma_1<\frac1{r^{11}},$$
--   and $n\in\mathbb N$ with $r^{11}+r^{10}-1\le n\le d-\frac{r+1}{\gamma_1}-1$. Then, with $\beta=c\,r^{-34}$ and $q_0=C\,r^C$: for all prime powers $q=p^m\ge q_0$, all groups $\Lambda$ without non-trivial elements of order $p$ and all irreducible $f\in\mathbb F_q[t]$ with $\deg f\ge2$, the $n$-skeleton of the KMS complex $X(A_d,\mathbb F_q,f)$ is a $(\beta,r,\Lambda)$-swap coboundary expander and a $\gamma_1$-local spectral expander.
--
--   Differences from the source:
--   - reading: 'q₀ ∈ ℕ large enough with respect to the other parameters, polynomial in r' and 'β > 0 which is of order 1/r³⁴' → ∃ c > 0, ∃ C ≥ 1 (natural) before r: q ≥ C·r^C and β = c/r³⁴; reason: the uniform reading: the proof's thresholds (Lemma 3.12, the choice of γ₂ from β₂) depend only on r, and any polynomial in r is dominated by C·r^C; c, C do not depend on r, d, γ₁, n, q, Λ or f
--   - reading: 'the n-skeleton of X(A_d, F_q, f) is a … γ₁-local spectral expander' → ((kmsX d F f).skeleton n).IsLocalSpectralExpander γ₁ (X^{≤n} itself); reason: literal reading of the printed sentence (Lemma 3.4 separately gives it for F^r(X^{≤n}))
--   - encoding: a prime power q = p^m and the field F_q → a finite field F (Fintype F) with q = Fintype.card F and p = ringChar F; reason: every finite field has prime-power order q and prime characteristic p; same instances
--   - encoding: groups Λ without non-trivial elements of order p → any group Λ (Type*) with ∀ g, g ^ ringChar F = 1 → g = 1; reason: p is prime, so g ≠ 1 with g^p = 1 has order exactly p; same groups
--   - encoding: X(A_d, F_q, f) = CC(SL_{d+1}(F_q[t]/(f)); (π_f(U_{[d]∖{i}}))_{i∈[d]}) with the uniform top-level distribution → kmsX d F f: cosetComplex over SL (Fin (d+1)) (AdjoinRoot f) of Hf d F f i = (U d F ([d]∖{i})).map (SpecialLinearGroup.map (AdjoinRoot.mk f)), vertices ⟨i, gH^f_i⟩ : Σ i, G ⧸ H^f_i, colour i; reason: Lean convention (0-based matrix indices, F_q[t]/(f) as AdjoinRoot f); the same complex and weights
--   - encoding: (β, r, Λ)-swap coboundary expander: F^r(X^{≤n}) is a (Λ, β) 1-coboundary expander (h⁰ ≥ β, h¹ ≥ β, H¹ = 1; Definitions 2.9, 2.12) → IsSwapCoboundaryExpander (c / r^34) r Λ with HZeroGe, HOneGe in ratio-free form and H1Trivial; reason: equivalent forms of h^k ≥ β (see the Cohomology definition)
--   - encoding: X^{≤n} with the inherited top-level distribution w_n → skeleton n weighted by the Garland weights of X; reason: the convention of p. 11
-- source:
--   Dikstein, Oppenheim, Valentiner-Branth, Polynomial Swap Coboundary Expansion with Applications to LTCs and PCPs, STOC 2027 submission (manuscript sha256 b9cb2095…), Theorem 3.1, p. 21 (proof §3.5, p. 30)

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Cohomology
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex

open Polynomial

universe u v

namespace PolySwap.KMS

/-- **Theorem 3.1**, p. 21. There are absolute constants `c > 0` and `C ≥ 1` (so that
`β = c·r⁻³⁴` and `q₀ = C·r^C`) such that: let `r ≥ 10⁴`, `d ≥ r⁵⁵`,
`(r+1)/(d − r¹¹ − r¹⁰ − 2) ≤ γ₁ < 1/r¹¹` and `r¹¹ + r¹⁰ − 1 ≤ n ≤ d − (r+1)/γ₁ − 1`. Then for
all prime powers `q = p^m ≥ q₀`, all groups `Λ` without non-trivial elements of order `p` and all
irreducible `f ∈ F_q[t]` with `deg f ≥ 2`, the `n`-skeleton of `X(A_d, F_q, f)` is a
`(β, r, Λ)`-swap coboundary expander and a `γ₁`-local spectral expander. -/
theorem theorem_3_1 : ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ, 1 ≤ C ∧
    ∀ r : ℕ, 10 ^ 4 ≤ r → ∀ d : ℕ, r ^ 55 ≤ d →
    ∀ γ₁ : ℝ, ((r : ℝ) + 1) / ((d : ℝ) - (r : ℝ) ^ 11 - (r : ℝ) ^ 10 - 2) ≤ γ₁ →
      γ₁ < 1 / (r : ℝ) ^ 11 →
    ∀ n : ℕ, r ^ 11 + r ^ 10 - 1 ≤ n → (n : ℝ) ≤ (d : ℝ) - ((r : ℝ) + 1) / γ₁ - 1 →
    ∀ (F : Type u) [Field F] [Fintype F], C * r ^ C ≤ Fintype.card F →
    ∀ (Λ : Type v) [Group Λ], (∀ g : Λ, g ^ ringChar F = 1 → g = 1) →
    ∀ f : F[X], Irreducible f → 2 ≤ f.natDegree →
      ((kmsX d F f).skeleton n).IsSwapCoboundaryExpander (c / (r : ℝ) ^ 34) r Λ ∧
      ((kmsX d F f).skeleton n).IsLocalSpectralExpander γ₁ := by sorry

end PolySwap.KMS
