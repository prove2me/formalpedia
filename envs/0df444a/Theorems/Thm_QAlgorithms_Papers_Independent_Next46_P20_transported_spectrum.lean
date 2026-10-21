-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P20_transported_spectrum
-- name    : QAlgorithms.Papers.Independent.Next46.P20.transported_spectrum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:21:01.553816+00:00
-- url     : https://prove2.me/theorems/5e9af6d6-fcf5-4b36-bef3-0bdbb0f071d1
-- title:
--   Eigenvalue correspondence and equality of full spectra
-- statement:
--   Let $n\ge1$, fix a unit window $\chi$, and transport a linear operator $a$ to $A$ on $\mathcal H_\chi$ with $D(A)=T_\chi D(a)$. For every $\lambda\in\mathbb C$ and $\Psi\in\mathcal H_\chi$,
--   $$
--   A\Psi=\lambda\Psi\iff
--   \exists\psi\in D(a):\quad\Psi=T_\chi\psi\ \text{and}\ a\psi=\lambda\psi.
--   $$
--   In addition, $\sigma(A)=\sigma(a)$ for the full spectra. A resolvent point means that $a-\lambda I$ is bijective from its domain onto the ambient Hilbert space and has an everywhere-defined bounded inverse; the same convention is used for $A$ on $\mathcal H_\chi$.
--
--   No compactness, discrete-spectrum, or boundedness assumption on $a$ is imposed.
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, PDF p. 10, Theorem 2.10

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF p.10, Theorem 2.10: correspondence of eigenvalue equations, together
with equality of the full unbounded spectra, rather than just point spectra. -/
theorem transported_spectrum {n : ℕ} (hn : 0 < n)
    (chi : ConfigurationL2 n) (hchi : ‖chi‖ = 1)
    (a : ConfigurationL2 n →ₗ.[ℂ] ConfigurationL2 n) :
    (∀ (lambda : ℂ) (Psi : windowSpace chi),
      ((Psi : PhaseL2 n), lambda • (Psi : PhaseL2 n)) ∈
        transportGraph chi (a.graph : Set (ConfigurationL2 n × ConfigurationL2 n)) ↔
      ∃ psi : ConfigurationL2 n,
        tensorEmbedding chi psi = (Psi : PhaseL2 n) ∧ (psi, lambda • psi) ∈ a.graph) ∧
    graphSpectrumOn (windowSpace chi) (transportGraph chi (a.graph : Set (ConfigurationL2 n × ConfigurationL2 n))) =
      graphSpectrumOn (⊤ : Submodule ℂ (ConfigurationL2 n)) (a.graph : Set (ConfigurationL2 n × ConfigurationL2 n)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P20

end
