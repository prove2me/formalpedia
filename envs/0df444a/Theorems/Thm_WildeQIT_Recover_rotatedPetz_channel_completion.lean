-- Prove2me | Theorems.Thm_WildeQIT_Recover_rotatedPetz_channel_completion
-- name    : WildeQIT.Recover.rotatedPetz_channel_completion
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-15T21:01:00.16605+00:00
-- url     : https://prove2.me/theorems/20e32730-8e95-47dc-b4a1-71a6d40b7934
-- title:
--   Trace preserving completion of a rotated Petz map on singular supports
-- statement:
--   Let $\sigma\succeq0$ be an operator on a finite dimensional complex input space, let $\mathcal N$ be a quantum channel in Kraus form, and fix a real rotation parameter $t$ and an input basis vector $a_0$. Write $E$ for the support projection of $\mathcal N(\sigma)$ and $\omega=|a_0\rangle\langle a_0|$. There exists a quantum channel $\widehat{\mathcal R}^{t}_{\sigma,\mathcal N}$ on the entire output matrix algebra satisfying
--
--   $$\widehat{\mathcal R}^{t}_{\sigma,\mathcal N}(Q)=\mathcal R^{t}_{\sigma,\mathcal N}(Q)+\operatorname{Tr}[(I-E)Q]\,\omega$$
--
--   for every matrix $Q$. The completed channel exactly recovers the reference operator:
--
--   $$\widehat{\mathcal R}^{t}_{\sigma,\mathcal N}(\mathcal N(\sigma))=\sigma.$$
--
--   Whenever $EQ=Q$, the completion agrees with the original rotated Petz map on $Q$. No full rank or trace normalization assumption on $\sigma$ is required. The fixed basis vector makes the input space nonempty. All operator powers use the support convention.
--
--   This is the single rotation version of the trace preserving completion used in Wilde's universal recovery channel, Eq. (12.111). It supplies a channel construction on singular supports; it does not assert the quantitative relative entropy or fidelity bounds, nor the continuous average over rotations.
-- source:
--   Supporting lemma for Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §12.3 pp.371–372 (Definition 12.3.2, Exercise 12.3.1, Proposition 12.3.1) and §12.5 p.379, Eqs.(12.111)–(12.115), https://arxiv.org/abs/1106.1445v8 . Single rotation specialization of the support complement completion; the source averages over rotations.

import Definitions.Def_WildeQIT_Recover_rotatedPetz
import Mathlib.Data.Matrix.Basis
open Matrix WildeQIT
open scoped ComplexOrder

namespace WildeQIT.Recover
theorem rotatedPetz_channel_completion {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (σ : Matrix a a ℂ) (hσ : σ.PosSemidef) (N : QChannel a b) (t : ℝ) (a0 : a) :
    ∃ R : QChannel b a,
      (∀ Q : Matrix b b ℂ, R.apply Q = rotatedPetz σ N t Q +
        Matrix.trace ((1-supportProj (N.apply σ))*Q) • Matrix.single a0 a0 (1 : ℂ)) ∧
      R.apply (N.apply σ)=σ ∧
      (∀ Q : Matrix b b ℂ, supportProj (N.apply σ)*Q=Q → R.apply Q=rotatedPetz σ N t Q) := by sorry
end WildeQIT.Recover
