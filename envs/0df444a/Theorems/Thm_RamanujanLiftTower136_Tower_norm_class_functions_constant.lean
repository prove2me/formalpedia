-- Prove2me | Theorems.Thm_RamanujanLiftTower136_Tower_norm_class_functions_constant
-- name    : RamanujanLiftTower136.Tower.norm_class_functions_constant
-- status  : Open
-- author  : @CGTMoyano
-- created : 2026-11-24T12:49:59.26251+00:00
-- url     : https://prove2.me/theorems/c849572c-f166-43ee-9243-863738b7a5fd
-- title:
--   Proof of Proposition 5.1 — functions factoring through the reduced norm are constant on $\mathrm{Cl}(E_n)$
-- statement:
--   Throughout, $F=\mathbb Q(\sqrt{17})$ with ring of integers $\mathcal O_F$, $D=\left(\frac{-1,-3}{F}\right)$ is the fixed totally definite quaternion algebra, $\mathcal O\subset D$ is the fixed maximal order of equation (3.7), and $Q=(2,\omega)$, $\omega=\frac{1+\sqrt{17}}2$, is the fixed prime ideal above $2$. For $n\ge0$ let $E_n$ be the Eichler order of equation (3.9) and $\mathrm{Cl}(E_n)$ its set of classes of locally principal right ideals.
--
--   Let $h$ be a complex function on ideal classes that factors through the reduced norm on $\mathrm{Cl}(E_n)$: $h([I])=h([J])$ whenever $I,J$ are locally principal right $E_n$-ideals with $\operatorname{nrd}(J)=x\operatorname{nrd}(I)$ for some totally positive $x\in F$. Then $h$ is constant on the class set:
--   $$h(c)=h(c')\qquad\text{for all }c,c'\in\mathrm{Cl}(E_n).$$
--
--   In the paper's words, the non-cuspidal subspace of the Brandt module $M_n=\{h:\mathrm{Cl}(E_n)\to\mathbb C\}$ consists exactly of the constants. This is what makes the Ramanujan–Petersson bound hold on the full complement $\mathbf 1^\perp$ of the constants, rather than only on a smaller cuspidal subspace.
--
--   Differences from the source:
--   - encoding: the fixed arithmetic objects → the shared concrete definitions over the quadratic algebra; reason: the representations preserve the field, the orders and all source instances
--   - encoding: norm-character functions $h([g])=\chi((\operatorname{nrd}(g_R))_R)$ on $D^\times\backslash\hat D^\times/U_n$ → functions on classes of right ideals depending only on the narrow class of the reduced norm ideal; reason: this is the linear span of the norm-character functions written in the ideal language of the shared definitions (see the definition's own note)
--   - restriction: only the implication "factors through the reduced norm $\Rightarrow$ constant" is stated; reason: the converse is immediate and is not used
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.19 (PDF p.20), proof of Proposition 5.1, paragraphs 2–3 ("We now show directly that every such function in our class space is constant ... Thus the noncuspidal subspace consists exactly of constants"). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_NormClasses

namespace RamanujanLiftTower136.Tower

theorem norm_class_functions_constant (n : ℕ) (h : IdealClass → ℂ)
    (hh : factorsThroughNorm (levelOrder n) h) (c c' : IdealClass)
    (hc : c ∈ classSet (levelOrder n)) (hc' : c' ∈ classSet (levelOrder n)) :
    h c = h c' := by sorry

end RamanujanLiftTower136.Tower
