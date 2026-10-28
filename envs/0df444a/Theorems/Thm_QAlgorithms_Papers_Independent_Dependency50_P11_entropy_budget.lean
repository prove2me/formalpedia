-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P11_entropy_budget
-- name    : QAlgorithms.Papers.Independent.Dependency50.P11.entropy_budget
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:37:31.916629+00:00
-- url     : https://prove2.me/theorems/3add145d-f7e8-4050-81f3-dfabcd3d7005
-- title:
--   Entropy budget for identical inputs
-- statement:
--   Let $d,m\ge1$ and let a device consist of a fixed unitary $U$ on $\mathbb C^m\otimes\mathbb C^d$ and an initial memory density matrix $\xi_1$. Let $\mathcal E$ be a completely positive, trace-preserving linear map. Suppose the first $n$ individual output channels equal $\mathcal E$ for every product-input history. For a density matrix $\rho$, feed $n$ independent identical copies into the device and let $\xi_{n+1}$ be its actual final memory marginal. Put $\Delta(\rho)=S(\rho)-S(\mathcal E(\rho))$, with natural-log von Neumann entropy. Then
--
--   $$n\Delta(\rho)\le S(\xi_{n+1})-S(\xi_1)\le\log m.$$
--
--   The statement includes $n=0$ and allows $\Delta(\rho)<0$. Memory may correlate with past outputs; each new input remains independent.
--
--   This bounds entropy decrease over a finite sequence by the available memory entropy.
-- source:
--   Repeatable quantum memory channels, arXiv:0808.3851v1, PDF p. 4, Section III, equation (3.7)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

/-- Section III, PDF p.4, (3.7): the actual memory entropy budget for n identical inputs.
Only n-repeatability is assumed; n=0 is included and Delta can be negative. -/
theorem entropy_budget {d m : ℕ} (hd : 0 < d) (D : MemoryDevice d m)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) (n : ℕ)
    (hRepeat : RepeatableFor D E n) (rho : Operator d) (hrho : IsDensityMatrix rho) :
    (n : ℝ) * entropyDecrease E rho ≤
      vonNeumannEntropy (memoryState D (fun _ => rho) n) - vonNeumannEntropy D.initial ∧
    vonNeumannEntropy (memoryState D (fun _ => rho) n) - vonNeumannEntropy D.initial ≤
      Real.log (m : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P11

end
