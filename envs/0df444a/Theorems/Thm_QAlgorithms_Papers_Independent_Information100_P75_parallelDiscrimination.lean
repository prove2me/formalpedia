-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_parallelDiscrimination
-- name    : QAlgorithms.Papers.Independent.Information100.P75.parallelDiscrimination
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:07:24.965415+00:00
-- url     : https://prove2.me/theorems/56e2f5f2-0b90-4c3b-b4a8-cf4d38cbd3b5
-- title:
--   Perfect parallel discrimination and the minimum number of copies
-- statement:
--   For a square complex matrix $X$, $W(X)$ denotes its numerical range, equivalently the values $\operatorname{Tr}(\sigma X)$ over PSD matrices $\sigma$ of trace one. Put $\Gamma_X=\{\theta\in[-\pi,\pi):\operatorname{Re}(e^{i\theta}X)\succeq0\}$, where $\operatorname{Re}Y=(Y+Y^\dagger)/2$, with Lebesgue length $|\Gamma_X|$ in radians. The ordinary width is $\operatorname{sw}(X)=\pi$ when $0\in W(X)$ and $\pi-|\Gamma_X|$ otherwise. For a complex subspace $\mathcal M$, $\operatorname{sw}^*(\mathcal M)=\inf_{X\in\mathcal M}\operatorname{sw}(X)$. The overlined width of a nonzero matrix is $\overline{\operatorname{sw}}(X)=\pi-|\Gamma_X|$.
--
--   Let $d,s\ge1$ and let $\Phi(X)=\sum_k A_kXA_k^\dagger$ and $\Psi(X)=\sum_l B_lXB_l^\dagger$ be channels with $\sum_k A_k^\dagger A_k=\sum_l B_l^\dagger B_l=I_d$. Put $\mathcal A=\operatorname{span}_{\mathbb C}\{B_l^\dagger A_k\}_{k,l}$. Perfect parallel discrimination with $N\ge1$ copies means that one normalized probe, allowed to be entangled with a finite noiseless reference, has orthogonal outputs under $\mathrm{id}\otimes\Phi^{\otimes N}$ and $\mathrm{id}\otimes\Psi^{\otimes N}$.
--
--   $$
--   (\exists N\ge1:\text{ perfect parallel discrimination})\iff\operatorname{sw}^*(\mathcal A)>0.
--   $$
--
--   When this width is positive, the least positive successful copy count is
--
--   $$N_0=\left\lceil\frac{\pi}{\operatorname{sw}^*(\mathcal A)}\right\rceil.$$
--
--   Discrimination succeeds at $N_0$ and fails at every integer $1\le N<N_0$. This characterizes both feasibility and the exact required number of simultaneous channel uses.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 5, Theorem 7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Theorem 7, PDF p.5, proof p.9: existence iff positive width, and the attained
least positive copy number. The reciprocal formula is restricted to positive width. -/
theorem parallelDiscrimination {d s r t : ℕ} (hd : 0 < d) (hs : 0 < s)
    (A : Fin r → Matrix (Fin s) (Fin d) ℂ) (B : Fin t → Matrix (Fin s) (Fin d) ℂ)
    (hA : IsKrausFamily A) (hB : IsKrausFamily B) :
    ((∃ N : ℕ, 1 ≤ N ∧ ParallelPerfect (krausApply A) (krausApply B) N) ↔
      0 < infWidth (crossSpace A B)) ∧
    (0 < infWidth (crossSpace A B) →
      let N0 := minimumCopies (krausApply A) (krausApply B)
      N0 = ⌈Real.pi / infWidth (crossSpace A B)⌉₊ ∧ 1 ≤ N0 ∧
        ParallelPerfect (krausApply A) (krausApply B) N0 ∧
        ∀ N : ℕ, 1 ≤ N → N < N0 → ¬ ParallelPerfect (krausApply A) (krausApply B) N) := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
