-- Prove2me | Theorems.Thm_QuantumSDP18_DensityBE_sandwich_eq_flag0
-- name    : QuantumSDP18.DensityBE.sandwich_eq_flag0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:30:27.350822+00:00
-- url     : https://prove2.me/theorems/e99bd026-9cbe-4496-886f-cf0dd2489307
-- title:
--   Proof of Lemma 12, display line 2 — the flag-one component vanishes
-- statement:
--   Let φ be any vector on the system, flag, and junk registers, and let φ₀ retain only its flag-zero amplitudes. The SWAP sandwich has the same value for φ and φ₀:
--
--   $$
--   (I\otimes\langle0|\langle\varphi|)S(I\otimes|0\rangle|\varphi\rangle)
--   =(I\otimes\langle0|\langle\varphi_0|)S(I\otimes|0\rangle|\varphi_0\rangle).
--   $$
--
--   Thus the flag-one part of the prepared state contributes no entry to this block. The identity applies before using purification or normalization.
--
--   **Formalization Note** The paper writes φ=α|ρ₀⟩+β|ρ₁⟩ with normalized components. Here φ₀ is the unnormalized vector α|ρ₀⟩, so the right-hand side incorporates the paper's α² factor.
-- source:
--   van Apeldoorn and Gilyén, Improvements in quantum SDP-solving with applications, arXiv:1804.05058v1, p. 16, proof of Lemma 12, opening sentence and display line 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BlockEncoding
import Definitions.Def_QuantumSDP18_DensityBE_Setting

namespace QuantumSDP18.DensityBE

theorem sandwich_eq_flag0 {w c : ℕ} (φ : Reg w c → ℂ) :
    sandwich φ = sandwich (flag0 φ) := by sorry

end QuantumSDP18.DensityBE
