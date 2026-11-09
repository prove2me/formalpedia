-- Prove2me | Theorems.Thm_QuantumOnePCA369_PauliPCA_pruning_energy
-- name    : QuantumOnePCA369.PauliPCA.pruning_energy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:40.264867+00:00
-- url     : https://prove2.me/theorems/4402ae87-5d13-4d8a-82ab-286073d70b33
-- title:
--   Lemma 4.2 — energy lost by projecting onto a top-$k$ eigenspace of a perturbed rank-one-plus-noise matrix
-- statement:
--   Let $\sigma=\lambda|v\rangle\langle v|+\nu\in\mathbb C^{d\times d}$ with $v\ne0$ (not necessarily a unit vector), $\lambda>0$ and $\nu\succeq0$; let $\hat\sigma=\sigma+\xi$ with $\xi$ Hermitian, and let $\Pi$ be the orthogonal projection onto a top-$k$ eigenspace of $\hat\sigma$ (any one, in case of degeneracy), $1\le k\le d$. There is a universal constant $C$ such that for every $t\ge\operatorname{tr}(\nu)$,
--   $$\|(I-\Pi)|v\rangle\|_2^2\le C\Big(\frac{t}{\lambda k}+\frac{k\|\xi\|_\infty^2}{\lambda(\lambda\langle v|v\rangle+t)}\Big).$$
--
--   This is the pruning step's stability estimate: keeping a top-$k$ eigenspace of the estimated block loses little of the target vector's energy, with an error quadratic in the perturbation norm.
--
--   **Formalization Note** The top-$k$ eigenspace projection is characterized by rank $k$, commutation with $\hat\sigma$, and a Rayleigh-quotient comparison between its range and kernel (see the Basic definition). The matrices are indexed by an arbitrary finite type.
--
--   Differences from the source:
--   - encoding: k ≤ d → 1 ≤ k ≤ d; reason: the bound t/(λk) is undefined at k = 0; a top-k eigenspace has positive dimension
--   - encoding: the orthogonal projection onto a top-k eigenspace (arbitrary in case of degeneracy) → IsTopKProj: rank-k orthogonal projection commuting with σ̂ whose range has Rayleigh quotients ≥ those of its kernel; reason: for Hermitian σ̂ these are exactly the projections onto top-k eigenspaces
--   - encoding: σ ∈ C^{d×d} → matrices indexed by any finite type ι with d = |ι|; reason: a relabeling of C^d
--   - encoding: ≲ → one universal constant C quantified before all data; reason: the source's constant is absolute
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 13, Lemma 4.2 (proof pp. 13–14)

import Mathlib
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic

open scoped ComplexOrder

namespace QuantumOnePCA369.PauliPCA

theorem pruning_energy :
    ∃ C : ℝ, ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) (lam t : ℝ)
      (ν ξ Pj : Matrix ι ι ℂ) (k : ℕ),
      v ≠ 0 → 0 < lam → ν.PosSemidef → ξ.IsHermitian → 1 ≤ k → k ≤ Fintype.card ι →
      IsTopKProj ((lam : ℂ) • Matrix.vecMulVec v (star v) + ν + ξ) Pj k →
      (Matrix.trace ν).re ≤ t →
      normSq2 ((1 - Pj).mulVec v) ≤
        C * (t / (lam * k) + k * opNorm ξ ^ 2 / (lam * (lam * normSq2 v + t))) := by sorry

end QuantumOnePCA369.PauliPCA
