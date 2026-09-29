-- Prove2me | Theorems.Thm_WeierstrassCurve_modularity_of_semistableModel
-- name    : WeierstrassCurve.modularity_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/8d28b1d1-1955-5262-800c-49fc64c476f6
-- title:
--   Modularity of semistable integral Weierstrass models
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, i.e. a tuple $(a_1,a_2,a_3,a_4,a_6)$ of integers, subject to two hypotheses: its discriminant satisfies $\Delta(W)\neq 0$ (no smoothness or minimality is assumed beyond this), and $W$ satisfies the project's predicate `IsSemistableModel`, which unfolds to: for every prime $p$ with $p \mid \Delta(W)$ one has $p \nmid c_4(W)$. The conclusion is that the base change $W$ to $\mathbb{Q}$ along `Int.castRingHom ℚ` satisfies the project's predicate `IsModular`. Unfolded, this asserts the existence of a Weierstrass curve $W_0$ over $\mathbb{Z}$ together with a variable change $C$ over $\mathbb{Q}$ carrying $W\otimes\mathbb{Q}$ to $W_0\otimes\mathbb{Q}$ (so $W_0$ is an integral model of the same rational curve, not necessarily minimal), and of an integer $N>0$ and a cusp form $f$ of weight $2$ on $\Gamma_0(N)$ in Mathlib's sense which is a normalised eigenform in the project's sense — the coefficients $a_n(f)$ of the $q$-expansion at $1$ satisfy $a_1(f)=1$, multiplicativity $a_{mn}(f)=a_m(f)a_n(f)$ for coprime $m,n$, the recursion $a_{p^{r+2}}(f)=a_p(f)a_{p^{r+1}}(f)-p\,a_{p^{r}}(f)$ for primes $p\nmid N$, and $a_{p^{r+2}}(f)=a_p(f)a_{p^{r+1}}(f)$ for primes $p\mid N$ — such that for every prime $p$ with $p\nmid\Delta(W_0)$ and $p\nmid N$ one has $a_p(f) = a_p(W_0)$ in $\mathbb{C}$, where $a_p(W_0) := p+1-\#\,(W_0\bmod p)(\mathbb{Z}/p)$, the point count being the cardinality of the Mathlib affine point type of the reduction of $W_0$ modulo $p$ (which includes the point at infinity). Thus modularity is expressed as an eigenform whose prime Fourier coefficients match the traces of Frobenius away from $\Delta(W_0)$ and $N$; nothing is asserted about $L$-functions, about $N$ being the conductor, or about the coefficients at bad primes.
--
--   This is Wiles's modularity theorem for semistable elliptic curves over $\mathbb{Q}$ (Wiles, and Taylor–Wiles for the Hecke-algebra input), in the shape in which the Frey curve needs it. It differs from the textbook statement in that semistability is replaced by the arithmetic condition that no prime divides both $\Delta$ and $c_4$ of the given integral model, the curve is a Weierstrass model with $\Delta\neq 0$ rather than an elliptic curve object, and the conclusion is the coefficient-by-coefficient agreement $a_p(f)=a_p(W_0)$ at primes away from $\Delta(W_0)N$ for some integral model $W_0$ and some level $N>0$, with no control of $N$. It is used to deduce [`FreyPackage.frey_isModular`](thm.html#FreyPackage.frey_isModular), the modularity of the Frey curve attached to a putative counterexample.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_modularity_of_semistableModel.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

theorem WeierstrassCurve.modularity_of_semistableModel (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) : (W.map (Int.castRingHom ℚ)).IsModular := by sorry
