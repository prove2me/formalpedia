-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P44_pureLoss_highEnergy_classical
-- name    : QAlgorithms.Papers.Independent.Gap48.P44.pureLoss_highEnergy_classical
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:43:00.365783+00:00
-- url     : https://prove2.me/theorems/d5af4f97-c32b-41a7-8d13-929f2ce52921
-- title:
--   High-energy assistance gap and ratio
-- statement:
--   Write $g_n(x)=(x+1)\ln(x+1)-x\ln x$ and $g_b(x)=g_n(x)/\ln2$ for $x\ge0$, with $0\ln0=0$. For $0<\eta<1$, put $c(N)=g_n(\eta N)$ and $c_E(N)=g_n(N)+g_n(\eta N)-g_n((1-\eta)N)$. Then
--
--   $$\lim_{N\to\infty}[c_E(N)-c(N)]=\ln\frac1{1-\eta},\qquad \lim_{N\to\infty}\frac{c_E(N)}{c(N)}=1,$$
--
--   and both $c(N)$ and $c_E(N)$ tend to $+\infty$. The ratio is unchanged by converting both rates to bits. This records a finite absolute assistance benefit along with a vanishing relative benefit.
-- source:
--   Quantum trade-off coding for bosonic communication, arXiv:1105.0119v4, PDF p. 7, §III C: high-energy assistance gap and capacity ratio

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P44

open Filter

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

/-- PDF p.7, Section III C: finite assistance gap, capacity ratio one, and
both diverging classical rates. Nats cancel in the ratio; bit rates have the same ratio. -/
theorem pureLoss_highEnergy_classical (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1) :
    Tendsto (fun budget : ℝ => g budget - g ((1 - eta) * budget))
      atTop (nhds (Real.log (1 / (1 - eta)))) ∧
    Tendsto (fun budget : ℝ =>
      (g budget + g (eta * budget) - g ((1 - eta) * budget)) / g (eta * budget))
      atTop (nhds 1) ∧
    Tendsto (fun budget : ℝ => g (eta * budget)) atTop atTop ∧
    Tendsto (fun budget : ℝ =>
      g budget + g (eta * budget) - g ((1 - eta) * budget)) atTop atTop := by sorry

end QAlgorithms.Papers.Independent.Gap48.P44

end
