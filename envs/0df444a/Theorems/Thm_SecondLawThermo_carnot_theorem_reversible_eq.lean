-- Prove2me | Theorems.Thm_SecondLawThermo_carnot_theorem_reversible_eq
-- name    : SecondLawThermo.carnot_theorem_reversible_eq
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:23.432036+00:00
-- url     : https://prove2.me/theorems/97574aca-2d93-4030-9987-de9c48a99c9e
-- title:
--   Carnot's theorem: all reversible engines between the same reservoirs are equally efficient
-- statement:
--   Throughout, $\Theta$ is a type of *empirical temperatures* carrying a linear order ($s<t$ means the reservoir at $s$ is colder than the one at $t$), and a **cycle** is a finitely supported function $c:\Theta\to\mathbb R$: for each reservoir temperature $t$, the number $c(t)$ is the net heat *absorbed by the device from* the reservoir at $t$ in one complete cycle (negative when heat is rejected to it), and only finitely many reservoirs are touched. The **work** delivered in the cycle is
--   $$W(c)=\sum_{t} c(t),$$
--   which is the first law for a device returning to its initial state. A set $\mathcal C$ of cycles stands for the physically realizable ones; it is assumed to be a convex cone: $0\in\mathcal C$, $c+d\in\mathcal C$ (run two devices side by side), and $r\cdot c\in\mathcal C$ for $r\ge 0$ (scale a device). A cycle is **reversible** when $c\in\mathcal C$ and $-c\in\mathcal C$. A cycle **operates between** $h$ and $k$ when $c(t)=0$ for every $t\notin\{h,k\}$. A **Carnot engine** between a hot reservoir $h$ and a cold reservoir $k$ is a reversible cycle operating between $h$ and $k$ with $c(h)>0$, $c(k)<0$ and $W(c)>0$. The **efficiency** relative to the hot reservoir is $\eta=W(c)/c(h)$.
--
--   **Statement.** Let $\mathcal C$ be a convex cone of realizable cycles satisfying the Clausius statement and let $k<h$. Any two Carnot engines $e,e'$ between $h$ and $k$ have the same efficiency:
--
--   $$\eta(e)=\eta(e').$$
--
--   This is the second clause of Carnot's theorem, and the article's starting point for the definition of thermodynamic temperature: "The efficiency of a quasi-static or reversible Carnot cycle depends only on the temperatures of the two heat reservoirs, and is the same, whatever the working substance."
-- source:
--   Wikipedia, "Second law of thermodynamics", revision oldid=1378607758, https://en.wikipedia.org/w/index.php?title=Second_law_of_thermodynamics&oldid=1378607758; sections "Carnot's principle" and "Carnot's theorem", second clause

import Definitions.Def_SecondLawThermo_Defs
import Mathlib

namespace SecondLawThermo

theorem carnot_theorem_reversible_eq {Θ : Type*} [LinearOrder Θ] (𝒞 : Set (Cycle Θ))
    (h𝒞 : IsCycleCone 𝒞) (hCl : ClausiusStatement 𝒞) (h k : Θ) (hkh : k < h)
    (e e' : Cycle Θ) (he : IsCarnotEngine 𝒞 e h k) (he' : IsCarnotEngine 𝒞 e' h k) :
    efficiency e h = efficiency e' h := by sorry

end SecondLawThermo
