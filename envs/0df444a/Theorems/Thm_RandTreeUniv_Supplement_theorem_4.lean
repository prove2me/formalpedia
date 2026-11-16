-- Prove2me | Theorems.Thm_RandTreeUniv_Supplement_theorem_4
-- name    : RandTreeUniv.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:39:01.743619+00:00
-- url     : https://prove2.me/theorems/bfdfc9b0-5824-4338-b658-10f253344fc9
-- title:
--   Theorem 4 — whp $G(n, C(\ln n)^\psi/n)$ contains every cycle factor of girth at least $K\ln n/(\psi\ln\ln n)$
-- statement:
--   For an integer $\ell$, let $\mathcal C_{n,\ell}$ be the family of all cycle factors on $[n]$ (spanning vertex-disjoint unions of cycles, i.e. 2-regular graphs on $[n]$) of girth at least $\ell$. A graph $G$ on $[n]$ is **$\mathcal C_{n,\ell}$-universal** if it contains a copy (not necessarily induced) of every member of $\mathcal C_{n,\ell}$ as a subgraph.
--
--   **Theorem.** There is $K_0$ such that for every $K\ge K_0$ there exists a constant $C>1$ with the following property. For every $\psi=\psi(n)\in\bigl[1,\frac{\ln n}{4\ln\ln n}\bigr]$ and every $\ell=\ell(n)$ with
--
--   $$
--   \ell\ \ge\ \frac{K\ln n}{\psi\ln\ln n},
--   $$
--
--   with high probability (probability tending to $1$ as $n\to\infty$) the random graph $G\sim G(n,C(\ln n)^\psi/n)$ is $\mathcal C_{n,\ell}$-universal.
--
--   This extends the universality result of Ferber, Kronenberg and Luh for cycle factors to sparse random graphs. The girth bound is tight up to a constant factor: by a union bound, $G(n,C(\ln n)^\psi/n)$ whp contains no $C_\ell$-factor for $\ell\le\ln n/((1+\varepsilon)\psi\ln\ln n)$.
--
--   **Formalization Note** $G(n,p)$ is the published `erProb n p`; universality is the published `IsUniversal` (non-induced containment, quantifier over all cycle factors inside the probability); $\mathcal C_{n,\ell}$ is `IsCycleFactorOfGirth ℓ` on `Fin n`. $C$ may depend on $K$ but not on $\psi$ or $\ell$. "With high probability" is uniform in $\psi$ and $\ell$: for every $\varepsilon>0$ there is $N$ such that for all $n\ge N$ and all admissible $\psi,\ell$ the probability is at least $1-\varepsilon$.
--
--   Differences from the source:
--   - reading: "Let K be a large enough constant" → ∃ K₀, ∀ K ≥ K₀, with C chosen after K and before ψ, ℓ and n; reason: the standard meaning of "large enough", in the paper's order of quantifiers
--   - reading: whp for fixed functions ψ(n), ℓ(n) → uniform over all admissible ψ and ℓ at each n (for every ε > 0 there is N such that …); reason: equivalent: a non-uniform failure yields functions ψ(n), ℓ(n) along which the paper's statement fails
--   - encoding: ℓ = ℓ(n) a (possibly real) girth bound → ℓ a natural number with (ℓ : ℝ) ≥ K ln n/(ψ ln ln n); reason: girth is an integer, so C_{n,ℓ} = C_{n,⌈ℓ⌉} and ⌈ℓ⌉ satisfies the same bound
--   - encoding: G(n,p) with p = p(n) a probability → published erProb n p, which clamps p to [0,1]; reason: the clamp is the identity on [0,1], and C(ln n)^ψ/n lies in [0,1] for all large n
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), Theorem 4, p.5 (PDF 6); C_{n,ℓ} defined p.5 (PDF 6) and §1.2, p.2 (PDF 3)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_RandTreeUniv_IsUniversal
import Definitions.Def_RandTreeUniv_Supplement_IsCycleFactorOfGirth

set_option autoImplicit false

open scoped Classical
open LPCommunity.SBMRecovery

namespace RandTreeUniv.Supplement

/-- **Theorem 4** (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal
linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.5
(PDF 6)). Let `K` be a large enough constant. There exists a constant `C > 1` satisfying that,
for every `ψ = ψ(n) ∈ [1, ln n/(4 ln ln n)]` and `ℓ = ℓ(n) ≥ K ln n/(ψ ln ln n)`, whp
`G ∼ G(n, C(ln n)^ψ/n)` is `C_{n,ℓ}`-universal, where `C_{n,ℓ}` is the family of all cycle factors
on `[n]` of girth at least `ℓ`.

**Formalization Note** Quantifiers: there is `K₀` such that for every `K ≥ K₀` there is `C > 1`
(chosen before `ψ` and `ℓ`) such that for every `ε > 0` there is `N` with: for all `n ≥ N`, all
`ψ` in the range and all integers `ℓ ≥ K ln n/(ψ ln ln n)`, the probability is at least `1 − ε`.
`ℓ` is a natural number (girth at least a real `ℓ` is girth at least `⌈ℓ⌉`). `G(n, p)` is the
published `erProb`; universality is the published `IsUniversal` (non-induced copies, all cycle
factors at once inside the probability); `C_{n,ℓ}` is `IsCycleFactorOfGirth ℓ`. -/
theorem theorem_4 :
    ∃ K₀ : ℝ, ∀ K : ℝ, K₀ ≤ K → ∃ C : ℝ, 1 < C ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ ψ : ℝ, 1 ≤ ψ → ψ ≤ Real.log n / (4 * Real.log (Real.log n)) →
        ∀ ℓ : ℕ, K * Real.log n / (ψ * Real.log (Real.log n)) ≤ ℓ →
          1 - ε ≤ erProb n (C * Real.log n ^ ψ / n)
            (fun G => RandTreeUniv.IsUniversal G (IsCycleFactorOfGirth ℓ)) := by sorry

end RandTreeUniv.Supplement
