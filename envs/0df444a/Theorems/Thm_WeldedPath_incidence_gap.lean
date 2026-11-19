-- Prove2me | Theorems.Thm_WeldedPath_incidence_gap
-- name    : WeldedPath.incidence_gap
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-18T16:16:43.747071+00:00
-- url     : https://prove2.me/theorems/dc8f80ec-7ad0-4c63-b4ec-59849d930f65
-- title:
--   Canonical completion-incidence kernel and spectral gap
-- statement:
--   Let $s,j$ be nonnegative integers with $3j\le s+1$, and let $\psi$ be a vector supported on injective databases of size $j$ over an $s$-element set. For an input $x$, define the normalized deletion incidence by
--
--   $$D_x=\sum_{I:\,x\notin\operatorname{dom}(I)} |I\rangle\langle +_{I,x}|,$$
--
--   where $|+_{I,x}\rangle$ is the uniform unit vector over the extensions of $I$ at $x$ (zero when there is no extension). Let $F|I\rangle=|I^{-1}\rangle$, let $\Gamma_j$ be the canonical completion map projected to level $j$, and put $K_j=\operatorname{ran}(\Gamma_j^\dagger)$. Then
--
--   $$\bigl(D_x\psi=D_xF\psi=0\text{ for every }x\bigr)\quad\Longleftrightarrow\quad\psi\in K_j,$$
--
--   and
--
--   $$\|\psi-\Pi_{K_j}\psi\|^2\le 2\sum_x\bigl(\|D_x\psi\|^2+\|D_xF\psi\|^2\bigr).$$
--
--   This identifies the completion space by its domain and image zero sums and bounds leakage from it by incidence energy. The degree-zero case is included.
-- source:
--   Carolan and Majenz, Compressed Permutation Oracles Revisited, https://arxiv.org/html/2609.28469v1, Lemma 4.11 and the incidence Laplacian argument (equation (46)), for the canonical WeldedPath completion operators in https://arxiv.org/html/2611.05912v1, equations (10)-(12). This supporting theorem proves the actual incidence gap and kernel identification; the quantitative one-query comparison is a separate estimate.

import Mathlib
import Definitions.Def_WeldedPath_exactCpO

set_option autoImplicit false
open Classical
open scoped BigOperators

namespace WeldedPath

theorem incidence_gap (s j : ℕ) (hsmall : 3*j ≤ s+1)
    (ψ : Hil (InjDb s)) (hsupport : ∀ I : InjDb s, I.size ≠ j → ψ I=0) :
    let D : Fin s → Hil (InjDb s) →L[ℂ] Hil (InjDb s) := fun x =>
      ∑ I ∈ Finset.univ.filter (fun I : InjDb s => I x=none),
        ketBra (ket I) (plusState I x)
    ((∀ x : Fin s, D x ψ=0 ∧ D x (flipDb s ψ)=0) ↔
      ψ∈(ContinuousLinearMap.adjoint (Gam s j)).range) ∧
    ‖ψ-((ContinuousLinearMap.adjoint (Gam s j)).range).starProjection ψ‖^2 ≤
      2*∑ x : Fin s, (‖D x ψ‖^2+‖D x (flipDb s ψ)‖^2) := by
  sorry

end WeldedPath
