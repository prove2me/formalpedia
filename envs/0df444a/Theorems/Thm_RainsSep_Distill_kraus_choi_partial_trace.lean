-- Prove2me | Theorems.Thm_RainsSep_Distill_kraus_choi_partial_trace
-- name    : RainsSep.Distill.kraus_choi_partial_trace
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:58:23.901402+00:00
-- url     : https://prove2.me/theorems/6e63ddf2-1ddc-4a96-9112-e93936172b80
-- title:
--   Eq. (12): $\mathrm{Tr}_W\big(\sum_i|P_i\rangle\langle P_i|\big)=\mathrm{Id}(V)$
-- statement:
--   Let $V,W$ be finite-dimensional Hilbert spaces and let $E_i:V\to W$ be Kraus operators of a superoperator, i.e. $\sum_i E_i^\dagger E_i=\mathrm{Id}(V)$. With $|E_i\rangle\in V\otimes W$ the vector of Eq. (7),
--
--   $$
--   \mathrm{Tr}_W\Big(\sum_i |E_i\rangle\langle E_i|\Big)=\mathrm{Id}(V).
--   $$
--
--   This is the trace-preservation condition rewritten in the vector picture. Applied to both halves of a product Kraus representation it gives Eq. (28), which in turn evaluates $B'_{\{0\}\cup S}$ in Eq. (29).
--
--   Differences from the source:
--   - encoding: Σ_i over the Kraus operators of a superoperator, V and W Hilbert spaces → a normalized Kraus family indexed by a finite type, V and W finite basis types; reason: finite dimension; every finite-dimensional superoperator has a finite Kraus representation and every normalized family is one (Reading 3)
--   - encoding: Tr_W(Σ_i |E_i⟩⟨E_i|) → the matrix with entries Σ_w Σ_i krausChoi (E i) (v, w) (v′, w); reason: this is the definition of the partial trace over W
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eq. (12), p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_RainsSep_Distill_krausChoi

open QAlgorithms

namespace RainsSep.Distill

/-- **Eq. (12): `Tr_W(Σ_i |P_i⟩⟨P_i|) = Id(V)`.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eq. (12), p. 2: "In particular, it follows that for a superoperator P,
Tr_W(Σ_i |P_i⟩⟨P_i|) = Id(V). (12)"

For finite-dimensional `V`, `W` and a normalized Kraus family `E_i : V → W`
(`Σ_i E_i† E_i = Id(V)`), the partial trace over `W` of `Σ_i |E_i⟩⟨E_i|` is the identity of `V`.

**Formalization Note.** The Kraus family is indexed by an arbitrary finite type (Reading 3 of the
mission: finite Kraus representations). -/
theorem kraus_choi_partial_trace {ι V W : Type*} [Fintype ι] [Fintype V] [Fintype W]
    [DecidableEq V] (E : ι → Matrix W V ℂ) (hE : IsKrausFamily E) :
    (Matrix.of fun v v' : V => ∑ w : W, ∑ i : ι, krausChoi (E i) (v, w) (v', w)) = 1 := by sorry

end RainsSep.Distill
