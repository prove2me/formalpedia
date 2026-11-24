-- Prove2me | Theorems.Thm_WeilConjectures_exists_bKer_indexing_of_off_range_src_fun
-- name    : WeilConjectures.exists_bKer_indexing_of_off_range_src_fun
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T05:09:37.533798+00:00
-- url     : https://prove2.me/theorems/433d83a8-599b-403c-afd6-e565ab467453
-- title:
--   Ker-Basis Indexing of Off-Range Source Values
-- statement:
--   Let $K$ be a field, $\iota$ a finite index type, and $M \in M_\iota(K[X])$. Given an embedding $e : \mathrm{Fin}\, n \hookrightarrow \iota$, a finite kernel basis $b_{\mathrm{ker}} : \mathrm{Fin}\, m \to \ker(\mathrm{toLin}' M)$, and a family $f$ whose off-range values lie in the kernel, there exists an equivalence
--   $$\sigma : \{i \mid i \notin \operatorname{range}(e)\} \simeq \mathrm{Fin}\, m$$
--   such that for every off-range index $i$,
--   $$f(i) = b_{\mathrm{ker}}(\sigma(i)).$$
--
--   This is the A62 bKer-strong off-range indexing (forbids zero-padding).
-- source:
--   Fintype.card; Equiv; LinearMap.ker.subtype; Hoffman–Kunze, Linear Algebra, Ch. 6

import Mathlib

/-- A62: off-range values of `f` are exactly the ker basis `bKer` up to a
finite equiv `σ` of the off-range subtype with `Fin m`.

**REUSE:** `Fintype.card`, `Equiv`, `LinearMap.ker.subtype`. -/

theorem WeilConjectures.exists_bKer_indexing_of_off_range_src_fun
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial K))
    {n : ℕ} (e : Fin n ↪ ι)
    {m : ℕ}
    (bKer : Module.Basis (Fin m) (Polynomial K)
      (LinearMap.ker (Matrix.toLin' M)))
    (f : ι → (ι → Polynomial K))
    (hker : ∀ i, (∀ j : Fin n, e j ≠ i) →
      f i ∈ LinearMap.ker (Matrix.toLin' M)) :
    ∃ (σ : {i : ι // ∀ j : Fin n, e j ≠ i} ≃ Fin m),
      ∀ i (h : ∀ j : Fin n, e j ≠ i),
        f i = (bKer (σ ⟨i, h⟩) : ι → Polynomial K) := by
  sorry
