-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P06_modularExpansion_specializations
-- name    : QAlgorithms.Papers.Independent.Independent1.P06.modularExpansion_specializations
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:45:31.504764+00:00
-- url     : https://prove2.me/theorems/bfe52410-0749-4ea8-83e6-49d17239203c
-- title:
--   §7: modular expansion and classical soundness
-- statement:
--   Let $G\in\mathbb F_2^{V\times E}$ have finite nonempty vertex and edge sets, with every column weight at most $\omega\in\mathbb N$. Let $t>0$ and $M,\rho\in\mathbb R$. Write $\mathrm{Mod}(W,t,M)$ for the modular cut inequality using the support union of $W$, and let $1_U$ indicate $U\subseteq V$. Then
--
--   $$\mathrm{Mod}(\langle1_U\rangle,t,M)\ \Longleftrightarrow\ |G^Tv|\ge M\min(t,|v\cap U|,|U\setminus v|)\quad(\forall v).$$
--
--   If $t\ge|V|$, the relative inequality at $U=V$ is equivalent to global expansion $|G^Tv|\ge M\min(|v|,|V|-|v|)$. If also the support union of $\ker G^T$ is all of $V$, then
--
--   $$\mathrm{Mod}(\ker G^T,t,\rho|E|/|V|)\ \Longleftrightarrow\ \frac{|G^Tv|}{|E|}\ge\frac{\rho}{|V|}d(v,\ker G^T)\quad(\forall v).$$
--
--   The last inequality, with locality $\omega$, is classical soundness $\rho$. The support condition implements the source's explicit $U=V$ specialization.
-- source:
--   Fast and fault-tolerant logical measurements: Auxiliary hypergraphs and transversal surgery, arXiv:2510.14895v1, §7, PDF p. 36. https://arxiv.org/abs/2510.14895v1 . PDF SHA-256: 5432b21da79d052ade1546bd9aa83b711bc517ad598c27fc785a711aeaafe54e.

import Definitions.Def_QAlgorithms_Defs_SurgeryFaultComplexes
import Definitions.Def_QAlgorithms_Defs_MitigationOperationBasis
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P06_Model
set_option autoImplicit false

/-!
# Fast and fault-tolerant logical measurements (arXiv:2510.14895v1)

Paper-local definitions and statement-only targets. Deferred nodes are recorded in the
assigned unit's HARD.md and GAPS.json. No operational fault-distance lower bound is
inferred from the open-boundary homology calculation.
-/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P06





































/-- Section 7 specializations, PDF p.36. The kernel is ker(G transpose). Positive
cardinalities exclude division by zero in the normalized classical definition. -/
theorem modularExpansion_specializations {V E : Type*} [Fintype V] [Fintype E]
    (G : Matrix V E F2) (U : Finset V) (t M rho : ℝ) (omega : ℕ)
    (tpositive : 0 < t) (vertices : 0 < Fintype.card V) (edges : 0 < Fintype.card E)
    (locality : ∀ e, hammingNorm (fun v => G v e) ≤ omega) :
    (HasModularExpansion G (Submodule.span F2 {restrictVertices U (fun _ => 1)}) t M ↔
      HasRelativeExpansion G U t M) ∧
    ((Fintype.card V : ℝ) ≤ t →
      ((HasRelativeExpansion G Finset.univ t M ↔ HasGlobalExpansion G M) ∧
       (addressed (LinearMap.ker G.transpose.mulVecLin) = Finset.univ →
        (HasModularExpansion G (LinearMap.ker G.transpose.mulVecLin) t
          (rho * Fintype.card E / Fintype.card V) ↔ HasClassicalSoundness G omega rho)))) := by sorry










end QAlgorithms.Papers.Independent.Independent1.P06
