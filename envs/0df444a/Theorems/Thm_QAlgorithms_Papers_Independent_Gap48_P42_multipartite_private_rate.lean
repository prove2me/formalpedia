-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P42_multipartite_private_rate
-- name    : QAlgorithms.Papers.Independent.Gap48.P42.multipartite_private_rate
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:36:47.490102+00:00
-- url     : https://prove2.me/theorems/077e1c28-c2a2-4b2b-915f-834c1e14fe89
-- title:
--   Corrected fixed-pair and optimized multipartite GHZ bounds
-- statement:
--   Let there be $N\ge2$ parties, a key dimension $d\ge2$, and positive finite local shield dimensions $s_1,\ldots,s_N$. Let $\rho$ be any positive semidefinite trace-one operator on the joint shield, and let $U_0,\ldots,U_{d-1}$ be arbitrary unitaries on that whole shield. Party $k$ owns its key and shield registers. The exact private state is
--
--   $$
--   \Gamma=\frac1d\sum_{i,j=0}^{d-1}|i,\ldots,i\rangle\langle j,\ldots,j|\otimes U_i\rho U_j^\dagger.
--   $$
--
--   For every ordered pair $i<j$, let $\eta_{ij}$ be the maximum of $|\langle f|U_i\rho U_j^\dagger|g\rangle|$ over product vectors whose every local factor has norm one. All these maxima are attained. For any choice of maximizing vectors $(f^{ij},g^{ij})$ for every pair, compute
--
--   $$
--   a_{ij}=\langle f^{ij}|U_i\rho U_i^\dagger|f^{ij}\rangle,\qquad
--   b_{ij}=\langle g^{ij}|U_j\rho U_j^\dagger|g^{ij}\rangle.
--   $$
--
--   They satisfy $a_{ij},b_{ij},\eta_{ij}>0$ and $\eta_{ij}\le\sqrt{a_{ij}b_{ij}}$. The balanced local success operators are contractions and yield exactly the unnormalized mixture $q_{ij}[p_{ij}\Phi^{ij}_++(1-p_{ij})\Phi^{ij}_-]$, of trace $q_{ij}$, where $\Phi^{ij}_\pm$ project onto $(|i,\ldots,i\rangle\pm|j,\ldots,j\rangle)/\sqrt2$. Set
--
--   $$
--   q_{ij}=\frac{2\min(a_{ij},b_{ij})}{d},\qquad
--   p_{ij}=\frac12+\frac{\eta_{ij}}{2\sqrt{a_{ij}b_{ij}}},\qquad
--   R_{ij}=q_{ij}[1-H_2(p_{ij})].
--   $$
--
--   Then $0<q_{ij}\le1$, $1/2<p_{ij}\le1$, and both the fixed-pair and optimized bounds hold:
--
--   $$
--   0<R_{ij}\le E_D(\Gamma)\quad(i<j),\qquad
--   0<\max_{i<j}R_{ij}\le E_D(\Gamma).
--   $$
--
--   Here $H_2$ is binary entropy in bits, and $E_D$ is the unconditional asymptotic vanishing-error GHZ rate per input copy under adaptive trace-preserving LOCC. The finite maximum retains the optimization over key pairs.
--
--   **Source corrections.** The printed rate uses $a_{\max}^{ij}$ and omits a factor two in the entropy argument. The two equal unnormalized diagonal entries are $\min(a_{ij},b_{ij})/d$, fixing both corrections. The mixture formula (2.6) itself already contains the correct outer $1/2$.
-- source:
--   Quantum states representing perfectly secure bits are always distillable, arXiv:quant-ph/0602176v2, PDF p. 3, II.B, Eqs. (2.5)–(2.6) and following bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P42

namespace QAlgorithms.Papers.Independent.Gap48.P42

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, Eq.(2.6) and fixed-pair/optimized bounds, note [11] p.5.
Source correction: printed a_max is replaced by 2 min(a_1,a_2)/d, and
printed 1/2+eta/sqrt(a_1*a_2) by 1/2+eta/(2 sqrt(a_1*a_2)). The computed
success output has both diagonal entries min(a_1,a_2)/d, forcing these changes.
The complete fixed-pair conclusions and finite maximum are retained. -/
theorem multipartite_private_rate {N d : ℕ} (hN : 2 ≤ N) (hd : 2 ≤ d)
    (S : Fin N → ℕ) (hS : ∀ k, 0 < S k)
    (rho : Matrix (PartyBasis S) (PartyBasis S) ℂ) (hrho : IsDensityMatrix rho)
    (U : Fin d → Matrix.unitaryGroup (PartyBasis S) ℂ) :
    (∀ p : KeyPair d, ∃ f g : ProductVectors S,
      Maximizes (shieldBlock rho U p.val.1 p.val.2) f g) ∧
    ∀ v : KeyPair d → ProductVectors S × ProductVectors S,
      (∀ p, Maximizes (shieldBlock rho U p.val.1 p.val.2) (v p).1 (v p).2) →
      (∀ p, PairConclusion rho U p.val.1 p.val.2 (v p).1 (v p).2) ∧
      0 < bestPairYield rho U v ∧
      ENNReal.ofReal (bestPairYield rho U v) ≤
        distillableGHZ (fun k => d * S k) (indexedPrivateDit rho U) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P42
