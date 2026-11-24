-- Prove2me | Theorems.Thm_WeilConjectures_ker_off_range_li_span
-- name    : WeilConjectures.ker_off_range_li_span
-- status  : Disproved
-- author  : @pageman
-- created : 2026-11-24T04:12:07.106329+00:00
-- url     : https://prove2.me/theorems/4cc09c7b-4530-4bcb-b41c-7a4bcc23bca0
-- title:
--   LI and Span of Ker-Extended Off-Range Source Family
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type, and $M \in M_\iota(K[X])$. Suppose $f : \iota \to K[X]^\iota$ agrees with on-range preimages $v_j$ on $\operatorname{range}(e)$, lands in $\ker(\mathrm{toLin}' M)$ off-range, satisfies the mapped equations against $b_{\mathrm{tgt}}$, and is compatible with a finite kernel basis $b_{\mathrm{ker}}$. Then $f$ is linearly independent and spans $K[X]^\iota$:
--   $$\operatorname{LinearIndependent}(f) \quad\text{and}\quad \top \le \operatorname{span}(\operatorname{range} f).$$
--
--   This is the A60 ker-off-range LI/span step.
-- source:
--   LinearIndependent; Submodule.span; Basis extension; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A60 KER-OFF-RANGE-LI: a source family `f` that agrees with on-range `v`,
lands in `ker (toLin' M)` off-range, and satisfies the mapped equations, is
linearly independent and spans the ambient module (via ker basis extension).

**REUSE:** `LinearIndependent`, `Submodule.span`, `Basis.mk`. -/

theorem WeilConjectures.ker_off_range_li_span
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial K))
    (d : ι → Polynomial K)
    {n : ℕ} (e : Fin n ↪ ι)
    (bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K))
    (v : Fin n → (ι → Polynomial K))
    {m : ℕ}
    (bKer : Module.Basis (Fin m) (Polynomial K)
      (LinearMap.ker (Matrix.toLin' M)))
    (f : ι → (ι → Polynomial K))
    (hmap : ∀ i, Matrix.toLin' M (f i) = d i • bTgt i)
    (hon : ∀ j, f (e j) = v j)
    (hker : ∀ i, (∀ j : Fin n, e j ≠ i) →
      f i ∈ LinearMap.ker (Matrix.toLin' M)) :
    LinearIndependent (Polynomial K) f ∧
      ⊤ ≤ Submodule.span (Polynomial K) (Set.range f) := by
  sorry
