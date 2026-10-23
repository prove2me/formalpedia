-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P38_coherence_iff_positive_advantage
-- name    : QAlgorithms.Papers.Independent.Information100.P38.coherence_iff_positive_advantage
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:03:31.414624+00:00
-- url     : https://prove2.me/theorems/0461c8db-a9ac-49ca-8866-81eb8b50a552
-- title:
--   Theorem 1
-- statement:
--   Let $d,n\ge1$, let $M=\{M_\mu\}_{\mu=1}^n$ be a POVM on $\mathbb C^d$, and let $H=\operatorname{diag}(E_0,\ldots,E_{d-1})$ have strictly increasing real energies. Coherence refers to this energy eigenbasis. Then
--
--   $$A_H^M>0\quad\Longleftrightarrow\quad \exists\mu:\ M_\mu\ne\Delta(M_\mu).$$
--
--   Here $A_H^M$ is the maximum over density matrices of observational ergotropy minus incoherent ergotropy. This makes positive advantage a faithful detector of measurement coherence. Zero effects contribute zero to coarse-graining.
-- source:
--   All coherent measurements provide observational ergotropic advantage, arXiv:2609.18735v1, PDF p. 5, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix

/-- Paper p.5, Theorem 1 (abstract p.1): coherence iff positive advantage.
Strictly ordered energies encode the paper's intended nondegenerate regime (p.10).
The erroneous zero-diagonal assertion about the coarse-grained witness in the printed
proof is neither a hypothesis nor a conclusion here. -/
theorem coherence_iff_positive_advantage {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (E : Fin d → ℝ) (hE : StrictMono E)
    (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (hM : IsPOVM M) :
    0 < observationalAdvantage E M ↔ ¬ measurementIncoherent M := by sorry

end QAlgorithms.Papers.Independent.Information100.P38

end
