-- Prove2me | Theorems.Thm_StabTestMem_phaseMoment_traceNorm_le
-- name    : StabTestMem.phaseMoment_traceNorm_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:13:27.999849+00:00
-- url     : https://prove2.me/theorems/30979aca-1ee6-4d5e-935c-319cc95a7b42
-- title:
--   Theorem 5.5 — $\|\rho_P-\sigma_P\|_1\le2^{-\Omega(n-t)}$ (corrected: t < n)
-- statement:
--   Let $\rho_P=\mathbb E_A[\psi_A^{\otimes t}]$ be the $t$-copy moment of a uniformly random degree-2 phase state and $\sigma_P=2^{-nt}\sum_{O\in\mathcal O_t}R(O)$. There are constants $c>0$ and $C$ such that for all $n$ and all $t<n$,
--
--   $$\|\rho_P-\sigma_P\|_1\le C\cdot2^{-c(n-t)} .$$
--
--   The phase-state ensemble can therefore be replaced by the combinatorial operator $\sigma_P$ when $t\ll n$.
--
--   Differences from the source:
--   - correction: the bound for all t → the hypothesis t < n; reason: for n = 1, ‖ρ_P − σ_P‖₁ ≥ Tr σ_P − 1 ≥ t!·2^{−t} − 1 (O_t contains the permutation matrices and Tr R(O) = 2^{n(t − rank(I+O))}, Eq. (91)), which outgrows C·2^{c(t−1)}; every use in the paper has t < n (Lemma 2.9, Lemma 5.6, Theorem 5.9)
--   - encoding: 2^{−Ω(n−t)} → C·2^{−c(n−t)} with c > 0 and C uniform in n, t; reason: the standard meaning of the asymptotic notation
--   - encoding: ‖·‖₁ → QAlgorithms.traceNorm (Re Tr √(M†M)); reason: the trace norm
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Theorem 5.5, Eq. (81), p. 39

import Definitions.Def_StabTestMem_rhoP
import Definitions.Def_StabTestMem_sigmaP
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

namespace StabTestMem

open QAlgorithms

/-- **Theorem 5.5: the phase-state moment is close to `σ_P` (corrected: `t < n`).** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Theorem
5.5, p. 39: "Let ρ_P := E_A[ψ_A^{⊗t}] be the ensemble average of t copies of a uniformly random degree
two phase state and σ_P = (1/2^{nt}) Σ_{O∈O_t} R(O). Then, ∥ρ_P − σ_P∥_1 ≤ 2^{−Ω(n−t)}. (81)"

There are constants `c > 0` and `C` such that for all `t < n`, `‖ρ_P − σ_P‖₁ ≤ C · 2^{−c(n − t)}`.

**Formalization Note.** Correction: the hypothesis `t < n` is added. Without it the bound fails:
for `n = 1`, `‖ρ_P − σ_P‖₁ ≥ Tr σ_P − 1 ≥ t!·2^{−t} − 1` (`O_t` contains the permutation matrices
and `Tr R(O) = 2^{n(t − rank(I+O))}`, Eq. (91)), which outgrows `C·2^{c(t−1)}`. Every use of
Theorem 5.5 in the paper has `t < n` (Lemma 2.9, Lemma 5.6, Theorem 5.9). `‖·‖₁` is the trace norm
`QAlgorithms.traceNorm` (`Re Tr √(M†M)`); `2^{−Ω(n−t)}` is `C·2^{−c(n−t)}` with `c, C` uniform in
`n, t`. -/
theorem phaseMoment_traceNorm_le :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ n t : ℕ, t < n →
      traceNorm (rhoP n t - sigmaP n t) ≤ C * (2 : ℝ) ^ (-c * ((n : ℝ) - t)) := by sorry

end StabTestMem
