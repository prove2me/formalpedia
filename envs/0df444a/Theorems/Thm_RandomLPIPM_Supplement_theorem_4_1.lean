-- Prove2me | Theorems.Thm_RandomLPIPM_Supplement_theorem_4_1
-- name    : RandomLPIPM.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:52:17.967027+00:00
-- url     : https://prove2.me/theorems/039b9b0b-b413-427a-a339-013a8a2b69f4
-- title:
--   Theorem 4.1 — moment bounds at the random projection scale
-- statement:
--   Let $T\succeq0$ be a deterministic $N\times N$ matrix and let $G\in\mathbb R^{m\times N}$ have independent $N(0,1)$ entries. Put
--   $$M=GTG^\top,\qquad \rho=\operatorname{Tr}(M^{-1}),\qquad \gamma=\frac{\operatorname{Tr}(M^{-2})}{\rho^2},$$
--   and let $f_T(t)=\operatorname{Tr}F_T(t)$ and $h_T(t)=\operatorname{Tr}H_T(t)$ be the resolvent traces, where $F_T(t)=tT(tT+I_N)^{-1}$ and $H_T(t)=F_T(t)(I_N-F_T(t))$. For a random variable $X$ write $\|X\|_{L^p}=(\mathbb E|X|^p)^{1/p}$.
--
--   Let $p\ge2$ be an integer and assume $\operatorname{rank}(T)-m\ge 4p+4$. Then $M$ is invertible almost surely, and
--
--   1. (resolvent trace concentration)
--   $$\big\|f_T(\rho)-m\big\|_{L^p}\le 8p;$$
--   2. (sensitivity–variance product concentration)
--   $$\big\|\gamma\,h_T(\rho)\big\|_{L^p}\le 20p.$$
--
--   The scale $\rho$ is random, and $f_T$, $h_T$ are evaluated at it. Since $\operatorname{Tr}\Pi=m$ for the Gaussian projection $\Pi=T^{1/2}G^\top M^{-1}GT^{1/2}$, the first bound says that at the scale $\rho$ the resolvent trace matches the trace of $\Pi$ up to $O(p)$; these moment bounds feed the proof of the Gaussian projection bound (Theorem 5.1).
--
--   **Formalization Note** The $L^p$ norm is Mathlib's extended-valued $L^p$ seminorm under the Gaussian law of $G$. The matrix inverse is total (zero on singular matrices), which affects $\rho,\gamma$ only on the event that $M$ is singular, which the first conclusion asserts is null.
--
--   Differences from the source:
--   - encoding: ‖X‖_{L^p} = (E|X|^p)^{1/p} ≤ 8p, 20p → eLpNorm X p under GaussianMatrix.gaussianMatrix m N, compared with ENNReal.ofReal (8p), ENNReal.ofReal (20p); reason: Lean's L^p seminorm is (E|X|^p)^{1/p} in [0, ∞], the same quantity
--   - encoding: M⁻¹ for invertible M → Mathlib's total matrix inverse (0 on singular matrices); reason: differs only on the null event that M is singular, which the first conclusion asserts is null
--   - encoding: rank(T) − m ≥ 4p + 4 → m + 4p + 4 ≤ rank T; reason: the same condition without natural-number truncation
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 4.1, p.24 (setting p.24; (17)-(18) p.23)

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_RandomLPIPM_traceF
import Definitions.Def_RandomLPIPM_traceH

open Matrix MeasureTheory

namespace RandomLPIPM.Supplement

/-- **Theorem 4.1 (Moment bounds at the random projection scale).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 4.1, p.24.

Setting (p.24): `T ⪰ 0` is a deterministic `N × N` matrix, `G ∈ ℝ^{m×N}` has independent `N(0,1)`
entries, `M := GTGᵀ`, `ρ := Tr(M⁻¹)`, `γ := Tr(M⁻²)/ρ²`, and `f_T`, `h_T` are the resolvent traces
(18), p.23. Let `p ≥ 2` be an integer and assume `rank(T) − m ≥ 4p + 4`. Then `M` is invertible
almost surely, and
`‖f_T(ρ) − m‖_{L^p} ≤ 8p` (resolvent trace concentration) and
`‖γ h_T(ρ)‖_{L^p} ≤ 20p` (sensitivity–variance product concentration).

**Formalization Note.** `‖X‖_{L^p} = (E|X|^p)^{1/p}` under the law `GaussianMatrix.gaussianMatrix m N`
of `G` (Mathlib's `eLpNorm`, valued in `ℝ≥0∞`). `ρ` and `γ` are random, and `f_T`, `h_T` are
evaluated at the random scale `ρ(G)`. `M⁻²` is `(M⁻¹)²`. Mathlib's matrix inverse is total (`0` on a
singular matrix), so `ρ`, `γ` take junk values exactly on the event that `M` is singular, which
the first conclusion asserts is null. The rank hypothesis is written without natural-number
truncation as `m + 4p + 4 ≤ rank T`. -/
theorem theorem_4_1 {N m : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosSemidef) (p : ℕ)
    (hp : 2 ≤ p) (hrank : m + 4 * p + 4 ≤ T.rank) :
    let M : (Fin m → Fin N → ℝ) → Matrix (Fin m) (Fin m) ℝ := fun G =>
      Matrix.of G * T * (Matrix.of G)ᵀ
    let ρ : (Fin m → Fin N → ℝ) → ℝ := fun G => trace (M G)⁻¹
    let γ : (Fin m → Fin N → ℝ) → ℝ := fun G => trace ((M G)⁻¹ * (M G)⁻¹) / ρ G ^ 2
    (∀ᵐ G ∂GaussianMatrix.gaussianMatrix m N, IsUnit (M G)) ∧
    eLpNorm (fun G => RandomLPIPM.traceF T (ρ G) - (m : ℝ)) (p : ENNReal)
        (GaussianMatrix.gaussianMatrix m N) ≤ ENNReal.ofReal (8 * p) ∧
    eLpNorm (fun G => γ G * RandomLPIPM.traceH T (ρ G)) (p : ENNReal)
        (GaussianMatrix.gaussianMatrix m N) ≤ ENNReal.ofReal (20 * p) := by sorry

end RandomLPIPM.Supplement
