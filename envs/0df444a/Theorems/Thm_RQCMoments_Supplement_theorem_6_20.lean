-- Prove2me | Theorems.Thm_RQCMoments_Supplement_theorem_6_20
-- name    : RQCMoments.Supplement.theorem_6_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:54:33.986598+00:00
-- url     : https://prove2.me/theorems/d1d77047-f290-45fd-9468-c4b1386d3005
-- title:
--   Theorem 6.20 — 1-locally invariant designs: $d_{TV}$ to Porter–Thomas is $\le C(k^{-1/2}+\varepsilon)$
-- statement:
--   For integers $n\ge2$, $k\ge2$ and $\varepsilon\in[0,1]$, let $\mu(k,\varepsilon)$ be any 1-locally invariant $\varepsilon$-approximate $n$-qubit unitary $k$-design, and for fixed $x,y\in\{0,1\}^n$ let $\nu(k,\varepsilon)$ be the distribution of $|\langle x|U|y\rangle|^2$ for $U\sim\mu(k,\varepsilon)$ and $\nu$ that for Haar random $U$. Then there is an absolute constant $C$ such that
--
--   $$d_{TV}\big(\nu(k,\varepsilon),\nu\big)\le C\big(k^{-1/2}+\varepsilon\big).$$
--
--   Local invariance on a single qubit already removes the discreteness barrier of Section 5 and gives total-variation convergence of single output probabilities.
--
--   **Formalization Note** $C$ is chosen before $n,k,\varepsilon,\mu,x,y$. $\mu$ is a measure on $U(2^n)$ with `IsLocallyInvariant 1 μ` (Definition 6.1) and `IsStrongDesign μ k k ε`. $d_{TV}$ is the published `totalVariationDistance`; $k^{-1/2}=1/\sqrt k$.
--
--   Differences from the source:
--
--   - encoding: ε-approximate unitary k-design (Remark 2.3) → IsStrongDesign μ k k ε (published; probability measure, literal completely positive order); reason: Remark 2.3 fixes this meaning; same instances
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 6.20, (303), p.59 (PDF p.61)

import Mathlib
import Definitions.Def_RQCMoments_IsStrongDesign
import Definitions.Def_RQCMoments_entry
import Definitions.Def_RQCMoments_Supplement_IsLocallyInvariant
import Definitions.Def_ProbabilityTheory_chapter_08_def_8_5_F000

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- **Theorem 6.20** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 6.20, (303), p.59, PDF p.61).
For integers `n ≥ 2` and `k ≥ 2` and `ε ∈ [0,1]`, let `μ(k, ε)` be the distribution of any 1-locally
invariant `ε`-approximate `n`-qubit unitary `k`-design, and for fixed `x, y ∈ {0,1}^n` let `ν(k, ε)`
be the distribution of `|⟨x|U|y⟩|²` for `U ∼ μ(k, ε)`. Let `ν` be the distribution of `|⟨x|U|y⟩|²` for
Haar random `U` on `n` qubits. Then there exists an absolute constant `C` such that
`d_TV(ν(k, ε), ν) ≤ C · (k^{−1/2} + ε)` (303).

**Formalization Note** `C` is chosen before `n, k, ε, μ, x, y`. `μ` is a measure on `U(2^n)` that is
1-locally invariant (Definition 6.1, `IsLocallyInvariant 1`) and `IsStrongDesign μ k k ε` (Remark 2.3).
Basis states `{0,1}^n` are `Fin (2^n)`. `d_TV` (3) is the published `totalVariationDistance`.
`k^{−1/2} = 1/√k`. -/
theorem theorem_6_20 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 2 ≤ k → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ μ : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ), IsLocallyInvariant 1 μ →
        IsStrongDesign μ k k ε → ∀ x y : Fin (2 ^ n),
          totalVariationDistance (μ.map (entry x y))
              ((QAlgorithms.Schur.unitaryHaar (2 ^ n)).map (entry x y)) ≤
            C * (1 / Real.sqrt k + ε) := by sorry

end Supplement

end RQCMoments
