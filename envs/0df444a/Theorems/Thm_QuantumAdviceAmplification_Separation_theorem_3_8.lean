-- Prove2me | Theorems.Thm_QuantumAdviceAmplification_Separation_theorem_3_8
-- name    : QuantumAdviceAmplification.Separation.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:04:51.966925+00:00
-- url     : https://prove2.me/theorems/85b89aee-59f6-48b9-8549-99f76b44299f
-- title:
--   Theorem 3.8 — Time-error tradeoff for random access codes
-- statement:
--   There are absolute constants $c_0,c_2,C\ge1$. For positive integers $m\le k$ and $t\ge c_0\log_2^2(2k)$, set $\varepsilon_1=H^{-1}(1-m/k)$ and $\eta=(\log_2t)/t+t/k$. There is a classical $k$-to-$m$ RAC whose decoder takes at most $t$ actual steps and whose error satisfies
--   $$\varepsilon\le\min\{1/2,\varepsilon_1+C\Phi(\varepsilon_1,\eta)\}\le\min\{1/2,\varepsilon_1+C\kappa\sqrt\eta,\varepsilon_1+C\kappa^2\eta/(1/2-\varepsilon_1)\}.$$
--   The code is either the trivial half-error code or Protocol 1 with $\ell=\lfloor t/c_2\rfloor$, $B=\lceil k/\ell\rceil$, $d=\lfloor(m-h)/B\rfloor$, and $2\le\ell<k$, restricting the message by filling the remaining block bits with zeros and padding the advice to exactly $m$ bits.
--
--   This is the complete coding-time tradeoff used by the language upper bound.
--
--   Differences from the source:
--   - encoding: F2 vectors with one-based coordinates, ell>=2 and 1<=d<=ell-1 → Bool coordinates with ZMod 2 arithmetic, zero-based Fin indices, and positive d,q with ell=q+d; reason: the Boolean/field and coordinate bijections preserve the source code and all parameter choices
--   - encoding: the absolute constants supplied in (33) and the parameters, restriction and padding of (32) → explicit existential cdec,c0,c2,C with (33), actual implementations, and a trivial-code or restrictPad alternative; reason: exposes the proof constants and exact code choice; positive d and payload length<=m prevent truncated subtraction from changing the floor formula
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.12, Theorem 3.8

import Definitions.Def_QuantumAdviceAmplification_Separation_parameters
set_option autoImplicit false
open Classical

namespace QuantumAdviceAmplification.Separation

theorem theorem_3_8 :
    ∃ cdec c0 c2 C : ℝ, 1 ≤ cdec ∧ ProtocolImplementations cdec ∧
      c2 = 2 * cdec ∧ c0 = 8 * cdec ∧ C = 10 * c2 + 2 * c2 / κ ^ 2 ∧
      1 ≤ c0 ∧ 1 ≤ c2 ∧ 1 ≤ C ∧
      ∀ k m t : ℕ, 0 < k → 0 < m → 0 < t → m ≤ k → c0 * (log₂ (2 * k)) ^ 2 ≤ t →
      ∃ (code : ClassicalCode k m) (ε : ℝ),
        0 ≤ ε ∧ ε ≤ 1 / 2 ∧ IsRAC code ε ∧ CodeRunsWithin code t ∧
        ε ≤ min (1 / 2) (optimumError k m + C * Φ (optimumError k m) (overhead k t)) ∧
        min (1 / 2) (optimumError k m + C * Φ (optimumError k m) (overhead k t)) ≤
          min (1 / 2) (min (optimumError k m + C * κ * Real.sqrt (overhead k t))
            (optimumError k m + C * κ ^ 2 * overhead k t / (1 / 2 - optimumError k m))) ∧
        (code = trivialCode k m ∨
          ∃ (S : BlockShape) (B : ℕ),
            S.ell = ⌊(t : ℝ) / c2⌋₊ ∧ 2 ≤ S.ell ∧ S.ell < k ∧
            B = ⌈(k : ℝ) / S.ell⌉₊ ∧ 0 < B ∧
            S.d = (m - headerLength S.ell) / B ∧
            k ≤ B * S.ell ∧ payloadLength S B ≤ m ∧
            code = restrictPad S B k m) := by sorry

end QuantumAdviceAmplification.Separation
