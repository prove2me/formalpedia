-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P42_schmidt_projection
-- name    : QAlgorithms.Papers.Independent.Support50.P42.schmidt_projection
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:12:32.212566+00:00
-- url     : https://prove2.me/theorems/a8070024-87b1-467c-9d15-366c5fdd1f57
-- title:
--   Exact Schmidt projection with matched local outcomes
-- statement:
--   Fix the common local Schmidt bases, a bias $p\in[0,1]$, and $n\ge0$ identical pairs in the normalized state $\sqrt{1-p}|00\rangle+\sqrt p|11\rangle$. Let $P_k$ project onto local strings of Hamming weight $k$, and write $D_k=\binom nk$. These projectors form a complete local instrument. Measuring both sides gives
--
--   $$\Pr(K_A=k,K_B=l)=\mathbf 1_{k=l}\binom nk(1-p)^{n-k}p^k.$$
--
--   Whenever this probability is positive, the conditional joint state is $D_k^{-1/2}\sum_{|x|=k}|x,x\rangle$, of norm one. Its reduced density is $P_k/D_k$, so its entanglement is $\log_2D_k$. Thus each local Schmidt rank is $D_k$; the tensor-product space has dimension $D_k^2$. This identifies precisely the concentrated resource before singlet standardization.
-- source:
--   Concentrating Partial Entanglement by Local Operations, arXiv:quant-ph/9511030v1, PDF p. 6, §II, Eqs.(5)–(6): exact Schmidt projection and matched outcomes

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P42

open scoped BigOperators Matrix ComplexConjugate

open MeasureTheory ProbabilityTheory

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact accepted objects, without introducing same-name aliases.

open Information100.P21 (Op Vec FiniteLOCC)

open Dependency50.P42 (dimensionedPower singlets)

open Dependency50.P48 (pureFidelity)

open Gap48.P32 (pairOfState)

open Next46.P39 (rectAct)

/-- PDF pp.5--6, Eqs.(5)--(6): matched local outcomes and exact conditional
maximally entangled type state. The printed 2*choose(n,k) joint dimension is
corrected to local rank choose(n,k); the tensor dimension is its square. -/
theorem schmidt_projection (n : ℕ) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    ‖schmidtBlock n p‖=1 ∧
    IsKrausFamily (fun k : Fin (n+1) => schmidtTypeProjector n k.val) ∧
    (∀ k l : Fin (n+1),
      ‖act (Matrix.kronecker (schmidtTypeProjector n k.val) (schmidtTypeProjector n l.val))
        (schmidtBlock n p)‖^2=if k=l then schmidtOutcomeWeight n p k.val else 0) ∧
    (∀ k : Fin (n+1), 0<schmidtOutcomeWeight n p k.val →
      ((Real.sqrt (schmidtOutcomeWeight n p k.val))⁻¹ : ℂ) •
        act (Matrix.kronecker (schmidtTypeProjector n k.val) (1 : Op (Fin n → Bool)))
          (schmidtBlock n p)=typeState n k.val ∧
      ‖typeState n k.val‖=1 ∧
      traceLeft (pureDensity (typeState n k.val))=
        ((n.choose k.val : ℂ)⁻¹) • schmidtTypeProjector n k.val ∧
      vnEntropy (traceLeft (pureDensity (typeState n k.val)))=Real.logb 2 (n.choose k.val : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P42

end
