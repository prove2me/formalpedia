-- Prove2me | Theorems.Thm_TightPQRepetition_Main_lemma_4_3
-- name    : TightPQRepetition.Main.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T23:42:30.381201+00:00
-- url     : https://prove2.me/theorems/19e14ce2-be4c-444a-ba95-d7c552cd404f
-- title:
--   Lemma 4.3 — statistical return-state replacement
-- statement:
--   Let $D_{0},D_{1}$ be efficiently sampleable and computationally indistinguishable to polynomial-size quantum adversaries with quantum advice. For every family of polynomial-size oracle circuits $V_\lambda$ acting as the identity on $R$ between oracle calls, and every family of polynomial-size normalized pure states $|\phi_\lambda\rangle_I$, put
--   $$|\psi_{b}\rangle=V_\lambda^{U_{b,\lambda}}|0\rangle_O|D_{b,\lambda}\rangle_{RE}|\phi_\lambda\rangle_I,\qquad\rho_{b,\lambda}=\mathrm{Tr}_{RE}\big(|D_{b,\lambda}\rangle\langle D_{b,\lambda}|\,|\psi_b\rangle\langle\psi_b|\,|D_{b,\lambda}\rangle\langle D_{b,\lambda}|\big).$$
--   Then
--   $$\|(I-|D_{0,\lambda}\rangle\langle D_{0,\lambda}|)_{RE}|\psi_0\rangle\|^2\,|0\rangle\langle0|\otimes|\bot\rangle\langle\bot|+|1\rangle\langle1|\otimes\rho_{0,\lambda}$$
--   and the same expression with $b=1$ are within a negligible function in trace distance.
--
--   The conclusion is statistical although the hypothesis is computational: this is what permits a later test that uses secret information.
--
--   Differences from the source:
--   - generalization: efficiently sampleable distributions → samplers given by polynomial-size circuit families; reason: a uniform sampler gives such a family
--   - encoding: the flagged state with registers flag and ⊥ → a density matrix on `Option` of the basis of OI, `none` being the failure branch; reason: the flag and ⊥ are orthogonal to the support of ρ, so the trace distance is the same
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Lemma 4.3 and footnote 12, printed p. 15 / PDF p. 17

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Oracle

namespace TightPQRepetition.Main

/-- Lemma 4.3 (printed p. 15, PDF p. 17). -/
theorem lemma_4_3 (c L i : ℕ → ℕ) (D : Bool → ℕ → Bits → Bits) (hD : IsSamplerPair c L D)
    (hind : CompIndist c c (D false) (D true))
    (C : (lam : ℕ) → OREICircuit (c lam) (L lam) (i lam)) (hC : IsOracleFamily c L i C)
    (φ : (lam : ℕ) → EuclideanSpace ℂ (QAlgorithms.Qubits (i lam)))
    (hφ : ∀ lam, QAlgorithms.IsState (φ lam)) :
    ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ lam,
      TD (flaggedReturn (c lam) (L lam) (i lam) (D false lam)
            (oracleOutput (c lam) (L lam) (i lam) (D false lam) (C lam) (φ lam)))
        (flaggedReturn (c lam) (L lam) (i lam) (D true lam)
            (oracleOutput (c lam) (L lam) (i lam) (D true lam) (C lam) (φ lam))) ≤ μ lam := by sorry

end TightPQRepetition.Main
