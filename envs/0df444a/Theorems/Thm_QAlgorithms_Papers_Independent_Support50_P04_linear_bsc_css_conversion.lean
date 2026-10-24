-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_linear_bsc_css_conversion
-- name    : QAlgorithms.Papers.Independent.Support50.P04.linear_bsc_css_conversion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:43:22.042615+00:00
-- url     : https://prove2.me/theorems/24c983ad-cc40-48f6-9467-1280dc277745
-- title:
--   Explicit linear-BSC-to-CSS code conversion
-- statement:
--   Let $n\ge1$, $0\le k\le n$, and let $H:\mathbb F_2^n\to\mathbb F_2^{n-k}$ be surjective. Let the injective linear encoder $c:\mathbb F_2^k\to\mathbb F_2^n$ have image $\ker H$, and let the classical syndrome decoder choose $u_0(s)$ with $Hu_0(s)=s$ for every syndrome. For $0\le\gamma\le1$, give errors $u$ probability $p_\gamma(u)=\prod_i[(1-\gamma)\mathbf1_{u_i=0}+\gamma\mathbf1_{u_i=1}]$. The CSS isometry is $V|m\rangle=|c_m\rangle_X$; its decoder measures the syndrome projector $P_s=\sum_{Hx=s}|x\rangle_X\langle x|$ and uses Kraus operators $V^\dagger Z^{u_0(s)}P_s$. There is an actual CPTP entanglement-transmission code with exactly these maps, $M=2^k$, and
--
--   $$F=2^{-k}\sum_{m\in\mathbb F_2^k}\sum_{u\in\mathbb F_2^n}p_\gamma(u)\,\mathbf1\{c_m+u-u_0(H(c_m+u))=c_m\}.$$
--
--   Thus the quantum squared entanglement fidelity equals the classical uniform-message average decoding success at the same block length and dimension.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 16, §V.B, pp.16–17

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF pp.16–17: explicit linear-BSC-to-CSS conversion.
Printed parity-check row count log n-log M; changed to n-k for binary [n,k] codes.
The syndrome-consistent decoder and all syndrome outcomes are retained. Its actual
entanglement fidelity equals the classical UNIFORM-message average success. -/
theorem linear_bsc_css_conversion {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (H : BinaryWord n →ₗ[ZMod 2] BinaryWord (n-k)) (hH : Function.Surjective H)
    (word : BinaryWord k →ₗ[ZMod 2] BinaryWord n) (hword : Function.Injective word)
    (hker : LinearMap.range word = LinearMap.ker H)
    (estimate : BinaryWord (n-k) → BinaryWord n) (hestimate : ∀ s, H (estimate s) = s)
    (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) :
    ∃ C : QAlgorithms.Papers.Independent.Information100.P80.TransmissionCode (Fin n → Fin 2) (Fin n → Fin 2),
      C.M = 2^k ∧
      HEq C.encoder (conjSuperop (cssIsometry word)) ∧
      HEq C.decoder (cssDecoder H word estimate) ∧
      QAlgorithms.Papers.Independent.Information100.P80.transmissionFidelity (piSuperop (fun _ : Fin n => (QAlgorithms.Papers.Independent.Information100.P27.qubitDephasing (1-2*gamma)))) C = classicalLinearSuccess gamma H word estimate := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
