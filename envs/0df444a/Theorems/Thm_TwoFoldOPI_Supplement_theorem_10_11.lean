-- Prove2me | Theorems.Thm_TwoFoldOPI_Supplement_theorem_10_11
-- name    : TwoFoldOPI.Supplement.theorem_10_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:10:48.599197+00:00
-- url     : https://prove2.me/theorems/a4ceddfc-219c-4be7-940b-b50bcc8764ee
-- title:
--   Theorem 10.11 — one-step stability of load sets
-- statement:
--   Let $B_1,\dots,B_R$ and $\alpha_1,\dots,\alpha_R$ be admissible with mean load $\eta$ and tilt $\nu$, and let $\mathcal T\subseteq[n]^m$ be a special-form load set: a partition $[n]=S_1\cup\dots\cup S_R$ with $|S_r|=\alpha_rn+O(1)$, $m=\eta n+O(1)$, and $B_a=B_r\cap\{0,\dots,m\}$ for $a\in S_r$. For all sufficiently large $n$, $\mathcal T$ is nonempty. Let $X$ be uniform on $\mathcal T$ and obtain $X'$ by replacing a uniformly chosen coordinate by an independent uniform symbol of $[n]$. With independent $(I_{\mathrm{src}},K_{\mathrm{src}})$, $\Pr[I_{\mathrm{src}}=r,K_{\mathrm{src}}=k]=\frac{\alpha_r}{\eta}k\Pr_{K\sim\mathrm{TiltPoiss}_{\nu,B_r}}[K=k]$, and $(I_{\mathrm{tar}},K_{\mathrm{tar}})\sim\mathrm{TiltPoiss}_{\nu,\{B_r\},\{\alpha_r\}}$,
--   $$\Pr[X'\in\mathcal T]=\Pr[K_{\mathrm{src}}-1\in B_{I_{\mathrm{src}}}]\,\Pr[K_{\mathrm{tar}}+1\in B_{I_{\mathrm{tar}}}]+O(n^{-1/2}),$$
--   where the implicit constant depends only on the load data, $\nu$, and the bounds in $|S_r|=\alpha_rn+O(1)$ and $m=\eta n+O(1)$.
--
--   Through the exit-probability identity of Section 9 this gives the Fourier-weight bound used by the quantum algorithms of Sections 11 and 12.
--
--   Differences from the source:
--   - encoding: |S_r| = α_r n + O(1), m = ηn + O(1), for all sufficiently large n, error O(n^{−1/2}) with the stated dependence → for all bounds b₁, b₂ there are C and n₀ such that for every n ≥ n₀, every partition with ||S_r| − α_r n| ≤ b₁ and every m with |m − ηn| ≤ b₂, T is nonempty and the error is at most C/√n; reason: explicit quantifiers; C and n₀ depend only on the load data, η, ν, b₁ and b₂
--   - encoding: B_a = B_r ∩ {0, …, m}; Pr[X′ ∈ T]; the product of the two probabilities → B_a = B_r (the same load set, since loads are at most m); stayProb T; pStay; reason: same quantities, Lean names
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §10.2, Theorem 10.11, p. 56

import Mathlib
import Definitions.Def_TwoFoldOPI_Supplement_Admissible
import Definitions.Def_TwoFoldOPI_Supplement_loadSet
import Definitions.Def_TwoFoldOPI_Supplement_stayProb
import Definitions.Def_TwoFoldOPI_Supplement_pStay

namespace TwoFoldOPI

namespace Supplement

/-- **Theorem 10.11 (one-step stability of load sets).**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §10.2, Theorem 10.11, p.56: "Assume B_1, …, B_R and α_1, …, α_R are admissible
(Definition 10.9) with mean load η and tilt ν, and define T ⊆ [n]^m as in Definition 10.10. For all
sufficiently large n, the set T is nonempty. Let X be uniform on T, and obtain X′ by replacing a
uniformly chosen coordinate of X by an independent uniform symbol in [n]. Define independent random
variables (I_src, K_src) and (I_tar, K_tar) by Pr[I_src = r ∧ K_src = k] =
(α_r/η) k Pr_{K∼TiltPoiss_{ν,B_r}}[K = k], (I_tar, K_tar) ∼ TiltPoiss_{ν,{B_r},{α_r}}. Then
Pr[X′ ∈ T] = Pr[K_src − 1 ∈ B_{I_src}] Pr[K_tar + 1 ∈ B_{I_tar}] + O(n^{−1/2}). The implicit constant
depends only on the fixed load data, the chosen tilt ν, and the bounds in |S_r| = α_r n + O(1) and
m = ηn + O(1)."; Definition 10.10, p.56 (special-form load sets).

For admissible load data with mean load `η` and tilt `ν` and for all bounds `b₁, b₂`, there are
`C` and `n₀` such that for every `n ≥ n₀`, every `m` with `|m − ηn| ≤ b₂` and every partition of
`[n]` (class map `part`) with `| |S_r| − α_r n | ≤ b₁`, the special-form load set
`T = {x ∈ [n]^m : c_a(x) ∈ B_{part a} ∀ a}` is nonempty and
`|Pr[X′ ∈ T] − p_stay| ≤ C/√n`, `p_stay = Pr[K_src − 1 ∈ B_{I_src}] · Pr[K_tar + 1 ∈ B_{I_tar}]`.

**Formalization Note.** `O(1)` bounds are `b₁, b₂`, chosen before `C` and `n₀`, which may depend only
on the load data, `η`, `ν`, `b₁`, `b₂`: this is the stated dependence of the constant, and "for all
sufficiently large n" uses the same `n₀`. `B_a = B_r ∩ {0, …, m}` and `B_a = B_r` give the same
`T` (`loadSet`). `Pr[X′ ∈ T]` is `stayProb T`, and `p_stay` is `pStay` (size-biased source law,
multi-class tilted Poisson target law, independent). Admissibility (`Admissible`) includes the
witness `ν`. -/
theorem theorem_10_11 {R : ℕ} (B : Fin R → Set ℕ) (α : Fin R → ℝ) (η ν : ℝ)
    (hadm : Admissible B α η ν) (b₁ b₂ : ℝ) :
    ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (m : ℕ) (part : Fin n → Fin R),
      (∀ r, |((Finset.univ.filter fun a => part a = r).card : ℝ) - α r * n| ≤ b₁) →
      |(m : ℝ) - η * n| ≤ b₂ →
      (loadSet m n fun a => B (part a)).Nonempty ∧
        |stayProb (loadSet m n fun a => B (part a)) - pStay B α η ν| ≤ C / Real.sqrt n := by sorry

end Supplement

end TwoFoldOPI
