-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P31_weakNoiseLeadingAdditivity
-- name    : QAlgorithms.Papers.Independent.Support50.P31.weakNoiseLeadingAdditivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:30:36.533579+00:00
-- url     : https://prove2.me/theorems/45fb4d6a-68ed-4099-83f2-12e7d23756a4
-- title:
--   Uniform leading norm multiplicativity and entropy additivity for weak noise
-- statement:
--   Fix $n\ge1$, positive dimensions $d_1,\ldots,d_n$, and a norm exponent $1\le p\le\infty$. For channels $\Phi_i$ on $d_i$-dimensional complex spaces define $\Psi_{i,\epsilon}=(1-\epsilon)\operatorname{Id}+\epsilon\Phi_i$ and $\Psi_\epsilon=\bigotimes_i\Psi_{i,\epsilon}$. Let $\nu_p$ be maximum output Schatten purity, $\nu_H$ minimum output natural entropy, and $\nu_\flat(\Phi)=\max_{\|v\|=1}\langle v,\Phi(|v\rangle\langle v|)v\rangle$. Then, uniformly over the channel tuple as $\epsilon\downarrow0$,
--   $$
--   \begin{aligned}
--   \nu_p(\Psi_\epsilon)-\prod_i\nu_p(\Psi_{i,\epsilon})&=o(\epsilon),\\
--   \nu_H(\Psi_\epsilon)-\sum_i\nu_H(\Psi_{i,\epsilon})&=o(\epsilon\log\epsilon),\\
--   \nu_\infty(\Psi_\epsilon)&=1-\epsilon\sum_i(1-\nu_\flat(\Phi_i))+o(\epsilon),\\
--   \nu_\infty(\Psi_{i,\epsilon})&=1-\epsilon+\epsilon\nu_\flat(\Phi_i)+o(\epsilon).
--   \end{aligned}
--   $$
--   Precisely, for each $\eta>0$ there is a cutoff $\delta>0$, chosen before the channels, such that for every channel tuple and $0<\epsilon<\min(\delta,1)$, the absolute residuals in the norm expansions are at most $\eta\epsilon$, and the entropy residual is at most $\eta|\epsilon\log\epsilon|$. The cutoff may depend on $n,(d_i),p,\eta$. This is leading-order additivity, without asserting exact equality for positive noise.
-- source:
--   On some additivity problems in quantum information theory, arXiv:math-ph/0003002v2, PDF p. 7, §4, Theorem: leading-order multiplicativity/additivity; equation (17)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31

noncomputable section

open Filter Asymptotics

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P31

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Gap48.P03 (holevoQuantity)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

open QAlgorithms.Papers.Independent.Dependency50.P44 (tensorChannels)

/-- PDF pp.7–9, Theorem and (17): leading norm multiplicativity and entropy
additivity uniformly over channel tuples. The cutoff precedes the channels and
may depend on fixed dimensions, n and p. Distinct norm and entropy scales. -/
theorem weakNoiseLeadingAdditivity {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (hd : ∀ i, 0 < d i)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    ∀ eta : ℝ, 0 < eta → ∃ delta : ℝ, 0 < delta ∧
      ∀ Phi : (i : Fin n) → Superop (Fin (d i)) (Fin (d i)),
      (∀ i, IsChannel (Phi i)) → ∀ eps : ℝ, 0 < eps → eps < delta → eps < 1 →
      (|nuP p (tensorChannels (fun i => weakNoise eps (Phi i))) -
          ∏ i, nuP p (weakNoise eps (Phi i))| ≤ eta * eps) ∧
      (|nuH (tensorChannels (fun i => weakNoise eps (Phi i))) -
          ∑ i, nuH (weakNoise eps (Phi i))| ≤ eta * |eps * Real.log eps|) ∧
      (|nuP ⊤ (tensorChannels (fun i => weakNoise eps (Phi i))) -
          (1 - eps * ∑ i, (1 - nuFlat (Phi i)))| ≤ eta * eps) ∧
      (∀ i, |nuP ⊤ (weakNoise eps (Phi i)) -
          (1 - eps + eps * nuFlat (Phi i))| ≤ eta * eps) := by sorry

end QAlgorithms.Papers.Independent.Support50.P31

end
