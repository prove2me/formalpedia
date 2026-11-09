-- Prove2me | Theorems.Thm_TriFormQ_lemma_2
-- name    : TriFormQ.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:52:14.947454+00:00
-- url     : https://prove2.me/theorems/98358558-614c-4256-b604-b897697ecede
-- title:
--   Lemma 2 (Lampert): $\mathbb E_{v\sim p_Z}q^{\mathrm{rk} f\langle v\rangle}=q^{\mathrm{AR}(f)}$
-- statement:
--   Let $f$ be a trilinear form on $\mathbb F_q^n$ with zero locus $Z$, fibers $Z_v$ and base-point distribution $p_Z(v)=|Z_v|/|Z|$. Then
--
--   $$\mathbb E_{v\sim p_Z}\,q^{\mathrm{rk} f\langle v\rangle}=\sum_{v\in\mathbb F_q^n}p_Z(v)\,q^{\mathrm{rk} f\langle v\rangle}=q^{\mathrm{AR}(f)}.$$
--
--   Equivalently, the average of $q^{\mathrm{rk} f\langle v\rangle}$ over a uniform $(u,v)\in Z$ is $q^{\mathrm{AR}(f)}$. Combined with Markov's inequality it shows that most of the $p_Z$-mass lies on good base points (Fact 1).
--
--   Differences from the source:
--   - encoding: the chain $\mathbb E_{(u,v)\in Z}q^{\mathrm{rk} f\langle v\rangle}=\mathbb E_{v\sim p_Z}q^{\mathrm{rk} f\langle v\rangle}=\sum_v p_Z(v)q^{\mathrm{rk} f\langle v\rangle}=q^{\mathrm{AR}(f)}\sum_v q^{-n}=q^{\mathrm{AR}(f)}$ → $\sum_v p_Z(v)q^{\mathrm{rk} f\langle v\rangle}=q^{\mathrm{AR}(f)}$; reason: the first two equalities are the definitions of the expectations and the fourth is an intermediate value; the chain asserts exactly this equality
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 2 (Lemma 2.1 in [Lam25]), p.14 (PDF p.17)

import Definitions.Def_TriFormQ_pZ
import Definitions.Def_TriFormQ_sliceV
import Definitions.Def_TriFormQ_AR

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 2 (Lemma 2.1 in [Lam25]),
p.14 (PDF p.17): "E_{(u,v)∈Z} q^{rk f⟨v⟩} := E_{v∼p_Z} q^{rk f⟨v⟩} = Σ_{v∈V} p_Z(v) q^{rk f⟨v⟩}
= q^{AR(f)} Σ_{v∈V} 1/qⁿ = q^{AR(f)}."

**Formalization Note.** The first equality is the definition of `p_Z`; the statement is the
equality of the sum with `q^{AR(f)}` (the intermediate `q^{AR(f)} Σ_v q^{−n}` equals it). -/
theorem lemma_2 {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (θ : TriForm F n) :
    ∑ v, pZ θ v * (Fintype.card F : ℝ) ^ (sliceV θ v).rank = (Fintype.card F : ℝ) ^ AR θ := by sorry

end TriFormQ
