-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_21
-- name    : PreservePast.Supplement.theorem_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:43:50.078534+00:00
-- url     : https://prove2.me/theorems/5bf2850e-0fa6-4a6f-87a9-d45d124b882f
-- title:
--   Theorem 21 — all-precision ROME response law
-- statement:
--   For $0<c<1$, $1\le k\le d$, $d\ge2$, histories are the $Z\in\mathbb R^{k\times d}$ with $ZZ^\top=I_k$, with covariance $C_Z=\begin{pmatrix}I_k&cZ\\cZ^\top&I_d\end{pmatrix}$. A query gives $a=(v,0)$, $v\in S^{k-1}$, and $y\in S^{m-1}$ and asks for
--   $$Ha=y,\qquad\operatorname{rank}H\le r,\qquad\|H\|_F\le R,\qquad J_{C_Z}(H)-J_{C_Z}(H^\ast)\le\varepsilon,$$
--   where $J_C(H)=\tfrac12\operatorname{tr}(HCH^\top)$ and $H^\ast$ is the equality-constrained oracle. Let $r\ge1$, $R\ge\sqrt{1+c^2}$, and $0<\delta<1/2$, and put $\alpha=2\varepsilon/c^2$. For $0<\alpha<1$,
--   $$B^\ast_{\mathrm{ROME}}=\Theta_{c,\delta}\big(k[1+d\log(1/\alpha)]\big).$$
--   The upper constant is independent of $c$ in this normalization. For $\alpha\ge1$ the minimum is zero; for $\alpha=0$ no finite budget suffices. Constants are uniform in $k,d,m,r,R,\alpha$ within the stated ranges.
--
--   The unknown association $Z$ determines the compensating direction of the edit, and this is what the retained state must encode.
--
--   **Formalization Note** The regret bound holds with probability $1-\delta$ for each fixed history and query, and exact fit, rank and norm hold on every outcome (the fixed-query convention of Appendix N). The output dimension is $m\ge1$. The logarithm is base two (§N.1).
--
--   Differences from the source:
--   - encoding: B*_ROME = Θ_{c,δ}(X) with upper constant independent of c and constants uniform in k, d, m, r, R, α → hi > 0 chosen after δ, lo > 0 after δ and c, both before the other parameters; lo·X ≤ B for every achieving width and an achieving protocol of width ≤ hi·X; reason: spells out the dependence of the constants; two-part form of a least width
--   - encoding: the minimum is zero; no finite budget suffices → a zero-bit achieving protocol exists; no protocol of any width achieves; reason: the meaning of the least width being zero or infinite
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 21, p.70 (PDF p.72), eq. (259); eqs. (255)–(258)

import Mathlib
import Definitions.Def_PreservePast_Supplement_RomeAchieves

open MeasureTheory

namespace PreservePast.Supplement

/-- **Theorem 21 (All-precision ROME response law).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 21, p.70 (PDF p.72), eq. (259);
the class and the request are (257)–(258).

Let `0 < c < 1`, `1 ≤ k ≤ d`, `d ≥ 2`, `r ≥ 1`, `R ≥ √(1 + c²)`, `0 < δ < 1/2` and
`α = 2ε/c²`. For `0 < α < 1`, `B*_ROME = Θ_{c,δ}(k[1 + d log(1/α)])`, with the upper constant
independent of `c`. For `α ≥ 1` the minimum is zero; for `α = 0` no finite budget suffices.

**Formalization Note.** The two-part form of the published goal: `lo · X ≤ B` for every achieving
width (arbitrary public coins, coin spaces in `Type`) and an achieving protocol of width
`≤ hi · X`. The upper constant `hi` is chosen after `δ` only ("The upper constant is independent
of c in this normalization"), the lower constant `lo` after `δ` and `c`; both before
`k, d, m, r, R, ε` ("Constants are uniform in k, d, m, r, R, α"). The tolerance is the binder `ε`
and `α = 2ε/c²` is written out. The output dimension satisfies `m ≥ 1` (the query has
`y ∈ S^{m−1}`). The logarithm is base two (§N.1). -/
theorem theorem_21 :
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∃ hi : ℝ, 0 < hi ∧ ∀ c : ℝ, 0 < c → c < 1 → ∃ lo : ℝ, 0 < lo ∧
      ∀ (k d m r : ℕ) (R ε : ℝ), 1 ≤ k → k ≤ d → 2 ≤ d → 1 ≤ m → 1 ≤ r →
        Real.sqrt (1 + c ^ 2) ≤ R →
        (0 < 2 * ε / c ^ 2 → 2 * ε / c ^ 2 < 1 →
          (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : Matrix (Fin k) (Fin d) ℝ → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k → ℝ) → (Fin m → ℝ) →
                Matrix (Fin m) (Fin k ⊕ Fin d) ℝ),
              RomeAchieves c r R ε δ P enc dec →
              lo * (k * (1 + d * Real.logb 2 (1 / (2 * ε / c ^ 2)))) ≤ (B : ℝ)) ∧
          ∃ B : ℕ, (B : ℝ) ≤ hi * (k * (1 + d * Real.logb 2 (1 / (2 * ε / c ^ 2)))) ∧
            ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
              (enc : Matrix (Fin k) (Fin d) ℝ → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k → ℝ) → (Fin m → ℝ) →
                Matrix (Fin m) (Fin k ⊕ Fin d) ℝ),
              RomeAchieves c r R ε δ P enc dec) ∧
        (1 ≤ 2 * ε / c ^ 2 →
          ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
            (enc : Matrix (Fin k) (Fin d) ℝ → Ω → Fin (2 ^ 0))
            (dec : Fin (2 ^ 0) → Ω → (Fin k → ℝ) → (Fin m → ℝ) →
              Matrix (Fin m) (Fin k ⊕ Fin d) ℝ),
            RomeAchieves c r R ε δ P enc dec) ∧
        (2 * ε / c ^ 2 = 0 →
          ∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
              (enc : Matrix (Fin k) (Fin d) ℝ → Ω → Fin (2 ^ B))
              (dec : Fin (2 ^ B) → Ω → (Fin k → ℝ) → (Fin m → ℝ) →
                Matrix (Fin m) (Fin k ⊕ Fin d) ℝ), ¬ RomeAchieves c r R ε δ P enc dec) := by sorry

end PreservePast.Supplement
