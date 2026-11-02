-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P64_sourceSchumacher
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P64.sourceSchumacher
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:36:02.956208+00:00
-- url     : https://prove2.me/theorems/c61f68f0-3e84-4e14-90f2-f0341e265a47
-- title:
--   Schumacher compression as source transfer
-- statement:
--   Let $|\phi\rangle^{RS}$ be a unit purification of a density matrix $\rho^S$ on a finite nonzero register $S$. A separate Source delivers $S$ to Alice and retains its inaccessible purifying reference $R$. All target registers are identified copies of $S$. With entropy measured in bits,
--
--   $$
--   \langle\mathrm{id}^{S\to\widehat A}:\rho^S\rangle+
--   H(S)_\rho[q\to q]\ge
--   \langle\mathrm{id}^{S\to\widehat B}:\rho^S\rangle.
--   $$
--
--   For every $\varepsilon,\delta>0$ and every sufficiently large positive $n$, physical local encoding and decoding maps transfer the purification to Bob, with joint full trace-norm error at most $\varepsilon$, using at most $\lfloor n(H(S)_\rho+\delta)\rfloor$ forward qubits. No Bell pairs or other nonlocal assistance are supplied. Local isometric dilations may retain work registers. Any additional generated Bell output may be discarded.
--
--   This expresses compression as preserving a Source-controlled quantum system. At entropy zero it permits sublinear communication; it does not assert a nontrivial zero-message finite-block channel.
-- source:
--   A triangle of dualities: reversibly decomposable quantum channels, source-channel duality, and time reversal, arXiv:quant-ph/0505138v1, PDF p. 3, Fully quantum Slepian-Wolf preamble: source formulation of compression

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P64

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P64

open QAlgorithms

open QAlgorithms.Papers.Independent.Gap48.P20
  (Copies redistributionMarginal subsystemEntropy forwardApply)

open QAlgorithms.Papers.Independent.Dependency50.P48 (densityPower)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, unnumbered compression display: the Source supplies rho at Alice;
H(S)_rho forward qubits per source copy suffice to transfer its full purification
to Bob. Rate zero permits sublinear communication. No input ebits are supplied. -/
theorem sourceSchumacher {R S : Type} [Fintype R] [Fintype S]
    [Nonempty R] [Nonempty S] (phi : EuclideanSpace ℂ (R × S))
    (hphi : IsState phi) :
    SourceTransferAchievable (sourceToAlice S) phi
      (vnEntropy (traceLeft (pureDensity phi))) 0 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P64

end
