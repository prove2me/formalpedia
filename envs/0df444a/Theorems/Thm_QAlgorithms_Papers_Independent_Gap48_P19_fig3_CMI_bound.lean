-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P19_fig3_CMI_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P19.fig3_CMI_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:13:07.961916+00:00
-- url     : https://prove2.me/theorems/6bcdb54f-7861-4821-a4b4-160a4bf27a42
-- title:
--   The Fig.3 CMI data-processing bound
-- statement:
--   Let $A,B,X,Y,L$ be finite nonempty alphabets with a probability law $w$ on $L$ and normalized stochastic kernels $k_X(x\mid l),k_Y(y\mid l),k_A(a\mid x),k_B(b\mid y)$. Construct exactly the Fig.3 law
--
--   $$p(a,b,x,y,l)=k_A(a\mid x)k_B(b\mid y)k_X(x\mid l)k_Y(y\mid l)w(l).$$
--
--   For its computed marginals and Shannon entropies in nats,
--
--   $$I_p(A:B\mid L)\le I_p(X:Y\mid L).$$
--
--   This retains the conditional independence of $X$ and $Y$ given $L$ in (39), and consequently both sides are zero. It records one lemma appearing as both (21) and (38), without asserting a broader hypothesis-free inequality.
-- source:
--   Entanglement of Distillation and Conditional Mutual Information, arXiv:quant-ph/0202144v2, PDF p. 8, Appendix A, Lemma A.2, Eq.(38); also Eq.(21)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19

namespace QAlgorithms.Papers.Independent.Gap48.P19

open scoped ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, (21), and pp.8-9, Lemma A.2, (38)-(46): the specific Fig.3 CMI bound.
Preserves factorization (39). Both CMIs vanish; no generalized postselection claim is made. -/
theorem fig3_CMI_bound {A B X Y L : Type}
    [Fintype A] [Fintype B] [Fintype X] [Fintype Y] [Fintype L]
    [Nonempty A] [Nonempty B] [Nonempty X] [Nonempty Y] [Nonempty L]
    (w : L → ℝ) (kx : L → X → ℝ) (ky : L → Y → ℝ)
    (ka : X → A → ℝ) (kb : Y → B → ℝ)
    (hw : IsLaw w) (hx : IsKernel kx) (hy : IsKernel ky)
    (ha : IsKernel ka) (hb : IsKernel kb) :
    let p := fig3Law w kx ky ka kb
    extensionClassicalCMI (lawMap p (fun z => (z.1.1, z.2))) ≤
      extensionClassicalCMI (lawMap p (fun z => (z.1.2, z.2))) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P19
